-- Prove2me | solution 1 for AvramDividend.Classical.chat04_arbitrary_history_full_future_path_markov_tonelli
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T10:16:58.904044+00:00
-- url     : https://prove2.me/submissions/126f0dd5-eff9-4784-8189-6f4631291cbd

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Process.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_full_shifted_future_path_indep_of_all_finite_cylinders

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
The unrestricted Tonelli factorisation of a measurable nonnegative payoff
of an arbitrary historical statistic and the whole future increment path.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {E : Type*} [MeasurableSpace E]
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0)
    (H : Ω → E) (hH : Measurable[𝓕 s] H)
    (hFinite : ∀ I : Finset ℝ≥0,
      IndepFun
        (fun ω (i : I) => X.X (s + (i : ℝ≥0)) ω - X.X s ω)
        H P)
    (f : E × (ℝ≥0 → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f (H ω,
        (fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω)) ∂P) =
    ∫⁻ h, ∫⁻ y, f (h, y)
      ∂(Measure.map
        (fun ω => (fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω)) P)
      ∂(Measure.map H P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let Y : Ω → (ℝ≥0 → ℝ) :=
    fun ω t => X.X (s + t) ω - X.X s ω
  have hHm : Measurable H := hH.mono (𝓕.le s) le_rfl
  have hYm : Measurable Y := by
    apply measurable_pi_iff.mpr
    intro t
    have ht : Measurable (X.X (s + t)) :=
      (X.adapted (s + t)).mono (𝓕.le (s + t)) le_rfl
    exact ht.sub ((X.adapted s).mono (𝓕.le s) le_rfl)
  have hFuture : IndepFun Y H P :=
    chat04_full_shifted_future_path_indep_of_all_finite_cylinders
      X s H hH hFinite
  have hIF : IndepFun H Y P :=
    (IndepFun_iff_Indep H Y P).2
      (((IndepFun_iff_Indep Y H P).1 hFuture).symm)
  have hJoint :=
    hIF.map_prod_eq_prod_map_map hHm.aemeasurable hYm.aemeasurable
  calc
    (∫⁻ ω, f (H ω, Y ω) ∂P) =
        ∫⁻ z, f z ∂(Measure.map (fun ω => (H ω, Y ω)) P) := by
          symm
          exact MeasureTheory.lintegral_map hf (hHm.prodMk hYm)
    _ = ∫⁻ z, f z ∂((Measure.map H P).prod (Measure.map Y P)) := by
          rw [hJoint]
    _ = ∫⁻ h, ∫⁻ y, f (h, y) ∂(Measure.map Y P) ∂(Measure.map H P) :=
          MeasureTheory.lintegral_prod f hf.aemeasurable
