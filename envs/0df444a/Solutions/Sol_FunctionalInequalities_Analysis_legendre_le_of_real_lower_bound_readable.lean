-- Prove2me | solution 1 for FunctionalInequalities.Analysis.legendre_le_of_real_lower_bound_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:34:57.024848+00:00
-- url     : https://prove2.me/submissions/6fb9709b-6f31-4b79-97de-652c66eb7f46

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_BoundedConjugate

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal Topology RealInnerProductSpace
open FunctionalInequalities
open FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A real floor and bounded effective domain give a finite upper bound for the
actual extended-real Legendre transform, at every primal point. -/
theorem solution
    (φ : E → EReal) (L : NNReal) (m : ℝ)
    (hbot : ∀ y, φ y ≠ ⊥)
    (hdom : ∀ y, φ y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ))
    (hfloor : ∀ y, (m : EReal) ≤ φ y) (x : E) :
    FunctionalInequalities.Analysis.legendre φ x ≤ (((L : ℝ) * ‖x‖ - m : ℝ) : EReal) := by
  classical
  unfold FunctionalInequalities.Analysis.legendre
  refine iSup_le ?_
  intro y
  by_cases hy : φ y = ⊤
  · simp [hy, sub_eq_add_neg]
  · have hyReal : ((φ y).toReal : EReal) = φ y :=
      EReal.coe_toReal hy (hbot y)
    have hm : m ≤ (φ y).toReal := by
      have hm' : (m : EReal) ≤ ((φ y).toReal : EReal) := by
        rw [hyReal]
        exact hfloor y
      exact_mod_cast hm'
    have hynorm : ‖y‖ ≤ (L : ℝ) := by
      simpa [mem_closedBall] using hdom y hy
    have hinner : inner ℝ y x ≤ (L : ℝ) * ‖x‖ :=
      (real_inner_le_norm y x).trans
        (mul_le_mul_of_nonneg_right hynorm (norm_nonneg x))
    calc
      (inner ℝ y x : EReal) - φ y =
          ((inner ℝ y x - (φ y).toReal : ℝ) : EReal) := by
            rw [EReal.coe_sub, hyReal]
      _ ≤ (((L : ℝ) * ‖x‖ - m : ℝ) : EReal) := by
        exact_mod_cast (sub_le_sub hinner hm)
