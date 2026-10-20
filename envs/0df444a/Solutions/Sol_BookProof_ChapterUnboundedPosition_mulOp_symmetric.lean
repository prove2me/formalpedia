-- Prove2me | solution 1 for BookProof.ChapterUnboundedPosition.mulOp_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-20T01:41:55.322371+00:00
-- url     : https://prove2.me/submissions/c333b6ce-770e-4fa8-aa65-996baebad4ed

-- Generated from ChapterUnboundedPosition.lean — solution of BookProof.ChapterUnboundedPosition.mulOp_symmetric
import Mathlib
import Definitions.Def_ChapterUnboundedPosition
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterUnboundedPosition



open scoped ENNReal InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite (L2Z)

set_option maxHeartbeats 1000000 in
theorem solution (f : ℤ → ℝ) (psi phi : mulDomain f) :
    ⟪mulOp f psi, (phi : L2Z)⟫_ℂ = ⟪(psi : L2Z), mulOp f phi⟫_ℂ := by
  -- `mulOp_apply` lives in the source chapter, not the def bundle: unfold it here.
  have mulOp_apply : ∀ (rho : mulDomain f) (k : ℤ),
      ((mulOp f rho : L2Z) : ℤ → ℂ) k = (f k : ℂ) * ((rho : L2Z) : ℤ → ℂ) k := fun _ _ => rfl
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun k => ?_
  simp only [mulOp_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring
