-- Prove2me | solution 1 for BookProof.ChapterUnboundedPosition.adjoint_eq_mulOp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-31T01:35:35.593102+00:00
-- url     : https://prove2.me/submissions/ceff8c24-4774-46a3-92c3-9ee903237bee

-- Generated from ChapterUnboundedPosition.lean — solution of BookProof.ChapterUnboundedPosition.adjoint_eq_mulOp
import Mathlib
import Definitions.Def_ChapterUnboundedPosition
import Theorems.Thm_BookProof_ChapterUnboundedPosition_mulOp_adjoint_apply
open BookProof.ChapterUnboundedPosition



open scoped ENNReal InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite (L2Z)

set_option maxHeartbeats 1000000 in
theorem solution (f : ℤ → ℝ) {phi eta : L2Z} (hphi : phi ∈ mulDomain f)
    (h : ∀ psi : mulDomain f, ⟪mulOp f psi, phi⟫_ℂ = ⟪(psi : L2Z), eta⟫_ℂ) :
    eta = mulOp f ⟨phi, hphi⟩ := by
    refine lp.ext (funext fun k => ?_)
    exact ((mulOp_adjoint_apply f h).1 k).symm

