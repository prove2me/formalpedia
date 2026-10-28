-- Prove2me | solution 1 for FunctionalInequalities.Probability.MomentMeasure.density_scaled_le_exp_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:38:23.619701+00:00
-- url     : https://prove2.me/submissions/9b9dbdb9-84b0-4dc9-8d0e-d713791281ec

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Coercivity

noncomputable section
open FunctionalInequalities.Analysis
section
open MeasureTheory Filter Set
open scoped ENNReal Topology
section Geometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Nonnegativity plus the actual linear lower bound controls the density after
scaling by max(M,1). This is where the small-integral protection is used. -/
theorem solution (φ : E → EReal) {c C M a : ℝ}
    (hC : 0 ≤ C) (ha : 1 ≤ a) (hMa : M ≤ a)
    (hlower : ∀ y, 0 ≤ FunctionalInequalities.Analysis.legendre φ y ∧ ((c * ‖y‖ - C * M : ℝ) : EReal) ≤ FunctionalInequalities.Analysis.legendre φ y)
    (y : E) : FunctionalInequalities.Probability.MomentMeasure.density (FunctionalInequalities.Analysis.legendre φ) (a • y) ≤ ENNReal.ofReal (Real.exp (C - c * ‖y‖)) := by
  have hb : ((c * ‖y‖ - C : ℝ) : EReal) ≤ FunctionalInequalities.Analysis.legendre φ (a • y) := by
    by_cases h : c * ‖y‖ - C ≤ 0
    · exact (EReal.coe_nonpos.mpr h).trans (hlower (a • y)).1
    · have hpos : 0 ≤ c * ‖y‖ - C := (lt_of_not_ge h).le
      have hs := mul_le_mul_of_nonneg_right ha hpos
      have hm := mul_le_mul_of_nonneg_left hMa hC
      have hnorm : ‖a • y‖ = a * ‖y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ a)]
      apply (EReal.coe_le_coe_iff.mpr (show c * ‖y‖ - C ≤ c * ‖a • y‖ - C * M by
        rw [hnorm]
        nlinarith)).trans (hlower (a • y)).2
  have he := EReal.exp_monotone (EReal.neg_le_neg_iff.mpr hb)
  simpa only [FunctionalInequalities.Probability.MomentMeasure.density, ← EReal.coe_neg, EReal.exp_coe, neg_sub] using he
