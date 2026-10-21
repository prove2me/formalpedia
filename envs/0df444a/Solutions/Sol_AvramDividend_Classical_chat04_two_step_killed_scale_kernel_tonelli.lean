-- Prove2me | solution 1 for AvramDividend.Classical.chat04_two_step_killed_scale_kernel_tonelli
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T10:06:36.658794+00:00
-- url     : https://prove2.me/submissions/8ed2b200-da24-426d-b63a-3b038959eccb

import Mathlib.Tactic.FunProp
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_levy_random_state_increment_product_law
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Two-step killed Markov transition: survival at the two observation times is
tracked explicitly. The process is still only grid-killed, without assuming
the unproved q-scale semigroup harmonicity or continuous-time survival.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (s t : ℝ≥0) (hst : s ≤ t) (x : ℝ) :
    (∫⁻ ω,
       if 0 ≤ x + X.X s ω ∧
          0 ≤ x + X.X s ω + (X.X t ω - X.X s ω)
       then ENNReal.ofReal
         (W (x + X.X s ω + (X.X t ω - X.X s ω)))
       else 0 ∂P) =
      ∫⁻ a, ∫⁻ b,
       if 0 ≤ x + a ∧ 0 ≤ x + a + b
       then ENNReal.ofReal (W (x + a + b))
       else 0
       ∂(Measure.map (X.X (t - s)) P)
       ∂(Measure.map (X.X s) P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let m : Ω → ℝ × ℝ :=
    fun ω => (X.X s ω, X.X t ω - X.X s ω)
  let f : ℝ × ℝ → ℝ≥0∞ :=
    fun z =>
      if 0 ≤ x + z.1 ∧ 0 ≤ x + z.1 + z.2
      then ENNReal.ofReal (W (x + z.1 + z.2))
      else 0
  have hXs : Measurable (X.X s) :=
    (X.adapted s).mono (𝓕.le s) le_rfl
  have hXt : Measurable (X.X t) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hm : Measurable m := by
    dsimp [m]
    exact hXs.prodMk (hXt.sub hXs)
  have hWm : Measurable W :=
    AvramDividend.Classical.chat03_scale_function_borel_measurable X q W hW
  have hA : MeasurableSet {z : ℝ × ℝ | 0 ≤ x + z.1} := by
    change MeasurableSet
      ((fun z : ℝ × ℝ => x + z.1) ⁻¹' Set.Ici (0 : ℝ))
    exact isClosed_Ici.measurableSet.preimage (by fun_prop)
  have hB : MeasurableSet {z : ℝ × ℝ | 0 ≤ x + z.1 + z.2} := by
    change MeasurableSet
      ((fun z : ℝ × ℝ => x + z.1 + z.2) ⁻¹' Set.Ici (0 : ℝ))
    exact isClosed_Ici.measurableSet.preimage (by fun_prop)
  have hSurvival : MeasurableSet
      {z : ℝ × ℝ | 0 ≤ x + z.1 ∧ 0 ≤ x + z.1 + z.2} :=
    hA.inter hB
  have hSum : Measurable (fun z : ℝ × ℝ => x + z.1 + z.2) := by
    fun_prop
  have hPayoff : Measurable
      (fun z : ℝ × ℝ => ENNReal.ofReal (W (x + z.1 + z.2))) :=
    ENNReal.measurable_ofReal.comp (hWm.comp hSum)
  have hf : Measurable f := by
    dsimp [f]
    exact Measurable.ite hSurvival hPayoff measurable_const
  have hProduct :
      Measure.map m P =
        (Measure.map (X.X s) P).prod
          (Measure.map (X.X (t - s)) P) := by
    simpa only [m] using
      AvramDividend.Classical.chat04_levy_random_state_increment_product_law
        X s t hst
  calc
    (∫⁻ ω,
       if 0 ≤ x + X.X s ω ∧
          0 ≤ x + X.X s ω + (X.X t ω - X.X s ω)
       then ENNReal.ofReal
         (W (x + X.X s ω + (X.X t ω - X.X s ω)))
       else 0 ∂P) =
      ∫⁻ ω, f (m ω) ∂P := by rfl
    _ = ∫⁻ z, f z ∂Measure.map m P :=
      (lintegral_map hf hm).symm
    _ = ∫⁻ z, f z ∂
        ((Measure.map (X.X s) P).prod
          (Measure.map (X.X (t - s)) P)) := by
      rw [hProduct]
    _ = ∫⁻ a, ∫⁻ b,
       if 0 ≤ x + a ∧ 0 ≤ x + a + b
       then ENNReal.ofReal (W (x + a + b))
       else 0
       ∂(Measure.map (X.X (t - s)) P)
       ∂(Measure.map (X.X s) P) := by
      simpa only [f] using (lintegral_prod f hf.aemeasurable)
