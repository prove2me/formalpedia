-- Prove2me | solution 1 for FunctionalInequalities.Analysis.lipschitzWith_real_legendre_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:34:54.872506+00:00
-- url     : https://prove2.me/submissions/2c0e89c2-c286-408e-b236-13df58c26375

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_BoundedConjugate

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal Topology RealInnerProductSpace
open FunctionalInequalities
open FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Bounded effective-domain slopes control the EReal supremum itself.
Only finite intercepts are converted to real numbers. -/
theorem solution
    (q : E → EReal) (L : NNReal) (ψ : E → ℝ)
    (hbot : ∀ y, q y ≠ ⊥)
    (hdom : ∀ y, q y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ))
    (hψ : ∀ x, FunctionalInequalities.Analysis.legendre q x = (ψ x : EReal)) :
    LipschitzWith L ψ := by
  classical
  apply LipschitzWith.of_le_add_mul L
  intro x z
  apply EReal.coe_le_coe_iff.mp
  rw [← hψ x]
  unfold FunctionalInequalities.Analysis.legendre
  refine iSup_le ?_
  intro y
  by_cases hy : q y = ⊤
  · simp only [hy, EReal.sub_top, bot_le]
  · have hyReal : ((q y).toReal : EReal) = q y :=
      EReal.coe_toReal hy (hbot y)
    have hterm : ((inner ℝ y z - (q y).toReal : ℝ) : EReal) ≤
        (ψ z : EReal) := by
      rw [EReal.coe_sub, hyReal, ← hψ z]
      exact le_iSup (fun w : E => (inner ℝ w z : EReal) - q w) y
    have hz : inner ℝ y z - (q y).toReal ≤ ψ z :=
      EReal.coe_le_coe_iff.mp hterm
    have hynorm : ‖y‖ ≤ (L : ℝ) := by
      simpa [mem_closedBall] using hdom y hy
    have hinner : inner ℝ y (x - z) ≤ (L : ℝ) * dist x z := by
      calc
        inner ℝ y (x - z) ≤ ‖y‖ * ‖x - z‖ :=
          real_inner_le_norm y (x - z)
        _ ≤ (L : ℝ) * ‖x - z‖ :=
          mul_le_mul_of_nonneg_right hynorm (norm_nonneg (x - z))
        _ = (L : ℝ) * dist x z := by rw [dist_eq_norm]
    rw [inner_sub_right] at hinner
    calc
      (inner ℝ y x : EReal) - q y =
          ((inner ℝ y x - (q y).toReal : ℝ) : EReal) := by
            rw [EReal.coe_sub, hyReal]
      _ ≤ ((ψ z + (L : ℝ) * dist x z : ℝ) : EReal) := by
        apply EReal.coe_le_coe_iff.mpr
        linarith only [hz, hinner]
