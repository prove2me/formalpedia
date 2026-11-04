-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_finite_grid_predictable_L1_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:58:43.487365+00:00
-- url     : https://prove2.me/submissions/50c3319c-2ba3-4605-a5d6-9a67e388de14

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_bounded_predictable_weight_count_condExp_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_weight_condExp_zero_implies_mean_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- A finite simple original-source predictable compensated marked-jump
integrand has zero physical mean when every actual finite-band count is
conditionally centred in the source right-continuous filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} (S : Finset ι)
    (s t : ι → ℝ≥0) (B : ι → Set ℝ)
    (J : ι → Ω → ℝ≥0∞)
    (hJsource : ∀ i ω, J i ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc (s i) (t i) ×ˢ B i))
    (rate : ι → ℝ≥0∞)
    (hYint : ∀ i ∈ S,
      Integrable (fun ω => (J i ω).toReal - (rate i).toReal) P)
    (hYcenter : ∀ i ∈ S,
      P[(fun ω => (J i ω).toReal - (rate i).toReal) |
        𝓕.rightCont (s i)] =ᵐ[P] 0)
    (H : ι → Ω → ℝ) (C : ι → ℝ)
    (hH : ∀ i ∈ S,
      StronglyMeasurable[𝓕.rightCont (s i)] (H i))
    (hBound : ∀ i ∈ S, ∀ᵐ ω ∂P, ‖H i ω‖ ≤ C i) :
    (∫ ω, ∑ i ∈ S,
      H i ω * ((J i ω).toReal - (rate i).toReal) ∂P) = 0 := by
  have hInt (i : ι) (hi : i ∈ S) :
      Integrable (fun ω =>
        H i ω * ((J i ω).toReal - (rate i).toReal)) P := by
    have hm : StronglyMeasurable (H i) :=
      (hH i hi).mono ((𝓕.rightCont).le (s i))
    exact (hYint i hi).bdd_mul hm.aestronglyMeasurable (hBound i hi)
  rw [integral_finset_sum S hInt]
  apply Finset.sum_eq_zero
  intro i hi
  have hConditional :=
    avram_p4_b_smalljump_original_bounded_predictable_weight_count_condExp_zero
      X (s i) (t i) (B i) (J i) (hJsource i)
      (rate i) (hYint i hi) (hYcenter i hi)
      (H i) (C i) (hH i hi) (hBound i hi)
  exact avram_p4_b_smalljump_original_predictable_weight_condExp_zero_implies_mean_zero
    X (s i) (t i) (B i) (J i) (hJsource i)
    (rate i) (H i) (hInt i hi) hConditional
