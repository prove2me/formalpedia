-- Prove2me | solution 1 for AvramDividend.Classical.chat04_arbitrary_history_next_grid_killed_scale_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T22:49:15.595464+00:00
-- url     : https://prove2.me/submissions/c48db22c-2788-40d5-9c6b-65b48a5d183a

import Mathlib.Tactic.FunProp
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_past_statistic_future_increment_product_law
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

attribute [local instance] Classical.propDecidable

/-!
General n-to-(n+1) grid-killed Markov transition step: an arbitrary
measurable path history H may include all previous grid observations,
the Boolean earlier-survival event S and current reserve R(H). Future
increment is independent of that entire history, not only the endpoint.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {E : Type*} [MeasurableSpace E]
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (s t : ℝ≥0) (hst : s ≤ t)
    (H : Ω → E) (hH : Measurable[𝓕 s] H)
    (S : Set E) (hS : MeasurableSet S)
    (R : E → ℝ) (hR : Measurable R) :
    (∫⁻ ω,
      if H ω ∈ S ∧ 0 ≤ R (H ω) + (X.X t ω - X.X s ω)
      then ENNReal.ofReal (W (R (H ω) + (X.X t ω - X.X s ω)))
      else 0 ∂P) =
      ∫⁻ z, ∫⁻ b,
        if z ∈ S ∧ 0 ≤ R z + b
        then ENNReal.ofReal (W (R z + b))
        else 0
        ∂(Measure.map (X.X (t - s)) P)
        ∂(Measure.map H P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let m : Ω → E × ℝ :=
    fun ω => (H ω, X.X t ω - X.X s ω)
  let f : E × ℝ → ℝ≥0∞ :=
    fun z =>
      if z.1 ∈ S ∧ 0 ≤ R z.1 + z.2
      then ENNReal.ofReal (W (R z.1 + z.2))
      else 0
  have hHm : Measurable H :=
    hH.mono (𝓕.le s) le_rfl
  have hXs : Measurable (X.X s) :=
    (X.adapted s).mono (𝓕.le s) le_rfl
  have hXt : Measurable (X.X t) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hm : Measurable m := by
    dsimp [m]
    exact hHm.prodMk (hXt.sub hXs)
  have hWm : Measurable W :=
    AvramDividend.Classical.chat03_scale_function_borel_measurable X q W hW
  have hHistorySet : MeasurableSet
      {z : E × ℝ | z.1 ∈ S} :=
    hS.preimage measurable_fst
  have hReserve : Measurable
      (fun z : E × ℝ => R z.1 + z.2) := by
    fun_prop
  have hNoExit : MeasurableSet
      {z : E × ℝ | 0 ≤ R z.1 + z.2} := by
    change MeasurableSet
      ((fun z : E × ℝ => R z.1 + z.2) ⁻¹' Set.Ici (0 : ℝ))
    exact isClosed_Ici.measurableSet.preimage hReserve
  have hGuard : MeasurableSet
      {z : E × ℝ | z.1 ∈ S ∧ 0 ≤ R z.1 + z.2} :=
    hHistorySet.inter hNoExit
  have hPayoff : Measurable
      (fun z : E × ℝ => ENNReal.ofReal (W (R z.1 + z.2))) :=
    ENNReal.measurable_ofReal.comp (hWm.comp hReserve)
  have hf : Measurable f := by
    dsimp [f]
    exact Measurable.ite hGuard hPayoff measurable_const
  have hProduct :
      Measure.map m P =
        (Measure.map H P).prod
          (Measure.map (X.X (t - s)) P) := by
    simpa only [m] using
      AvramDividend.Classical.chat04_past_statistic_future_increment_product_law
        X s t hst H hH
  calc
    (∫⁻ ω,
      if H ω ∈ S ∧ 0 ≤ R (H ω) + (X.X t ω - X.X s ω)
      then ENNReal.ofReal (W (R (H ω) + (X.X t ω - X.X s ω)))
      else 0 ∂P) =
      ∫⁻ ω, f (m ω) ∂P := by rfl
    _ = ∫⁻ z, f z ∂(Measure.map m P) :=
      (lintegral_map hf hm).symm
    _ = ∫⁻ z, f z ∂
        ((Measure.map H P).prod
          (Measure.map (X.X (t - s)) P)) := by
      rw [hProduct]
    _ = ∫⁻ z, ∫⁻ b,
        if z ∈ S ∧ 0 ≤ R z + b
        then ENNReal.ofReal (W (R z + b))
        else 0
        ∂(Measure.map (X.X (t - s)) P)
        ∂(Measure.map H P) := by
      simpa only [f] using (lintegral_prod f hf.aemeasurable)
