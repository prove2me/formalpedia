-- Prove2me | solution 1 for BookProof.ChapterUnboundedPosition.mulOp_adjoint_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-31T02:04:44.854978+00:00
-- url     : https://prove2.me/submissions/24a75f1b-5bd8-4b5e-9c55-466894e99bc3

-- Generated from ChapterUnboundedPosition.lean — solution of BookProof.ChapterUnboundedPosition.mulOp_adjoint_apply
import Mathlib
import Definitions.Def_ChapterUnboundedPosition
import Theorems.Thm_BookProof_ChapterUnboundedPosition_single_mem_mulDomain
import Theorems.Thm_BookProof_ChapterUnboundedPosition_mulOp_single
import Theorems.Thm_BookProof_ChapterUnboundedPosition_inner_single_left
open BookProof.ChapterUnboundedPosition



open scoped ENNReal InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite (L2Z)

set_option maxHeartbeats 1000000 in
theorem solution (f : ℤ → ℝ) {phi eta : L2Z}
    (h : ∀ psi : mulDomain f, ⟪mulOp f psi, phi⟫_ℂ = ⟪(psi : L2Z), eta⟫_ℂ) :
    (∀ k, (f k : ℂ) * (phi : ℤ → ℂ) k = (eta : ℤ → ℂ) k) ∧ phi ∈ mulDomain f := by
    have hpt : ∀ k, (f k : ℂ) * (phi : ℤ → ℂ) k = (eta : ℤ → ℂ) k := by
      intro k
      have hk := h ⟨lp.single 2 k (1 : ℂ), single_mem_mulDomain f k 1⟩
      rw [mulOp_single f k (1 : ℂ), inner_single_left, inner_single_left] at hk
      simpa [Complex.conj_ofReal] using hk
    refine ⟨hpt, ?_⟩
    change Memℓp _ 2
    have hfun : (fun k => (f k : ℂ) * (phi : ℤ → ℂ) k) = (eta : ℤ → ℂ) := funext hpt
    rw [hfun]
    exact lp.memℓp eta

