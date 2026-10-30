-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_killed_survival_discounted_scale_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:56:20.199698+00:00
-- url     : https://prove2.me/submissions/c150ae87-9793-44f1-b420-cc9e319ae4b9

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_unbounded_deterministic_killed_qscale
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_scale_fixed_time_integrable
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_lower_survival_measurable_no_schedule
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Genuine unbounded-variation killed ENNReal expectation follows from the
accepted real P-law semigroup, using actual integrability and positivity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (x : ℝ) (t : ℝ≥0) :
    (∫⁻ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω))) ω ∂P) =
      ENNReal.ofReal (W x) := by
  let S : Set Ω := {ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}
  let f : Ω → ℝ := fun ω =>
    Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)
  have hS : MeasurableSet S :=
    chat04_shifted_lower_survival_measurable_no_schedule X x t
  have hIntRaw : Integrable (fun ω => W (x + X.X t ω)) P :=
    chat04_unbounded_scale_fixed_time_integrable X q hq W hW hnbv x t
  have hInt : Integrable (S.indicator f) P :=
    (hIntRaw.const_mul (Real.exp (-(q * (t : ℝ))))).indicator hS
  have hWzero : W 0 = 0 :=
    chat04_scale_zero_origin_of_unbounded_variation X hnbv q hq W hW
  have hWnn (z : ℝ) (hz : 0 ≤ z) : 0 ≤ W z := by
    rcases hz.eq_or_lt with heq | hpos
    · simpa [← heq] using le_of_eq hWzero.symm
    · exact (scaleFunction_strict_pos_of_unbounded_variation
        X q W hW hnbv z hpos).le
  have hN : 0 ≤ᵐ[P] S.indicator f := by
    filter_upwards with ω
    by_cases hw : ω ∈ S
    · rw [Set.indicator_of_mem hw]
      exact mul_nonneg (Real.exp_nonneg _) (hWnn _ (hw t le_rfl))
    · simp [Set.indicator_of_notMem hw]
  calc
    (∫⁻ ω, S.indicator (fun ω => ENNReal.ofReal (f ω)) ω ∂P) =
        ∫⁻ ω, ENNReal.ofReal (S.indicator f ω) ∂P := by
      apply lintegral_congr
      intro ω
      by_cases hw : ω ∈ S
      · simp only [Set.indicator_of_mem hw]
      · simp only [Set.indicator_of_notMem hw, ENNReal.ofReal_zero]
    _ = ENNReal.ofReal (∫ ω, S.indicator f ω ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal hInt hN).symm
    _ = ENNReal.ofReal (W x) := by
      congr 1
      exact avram_root29_01_unbounded_deterministic_killed_qscale
        X hnbv q hq W hW x t
