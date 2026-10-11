-- Prove2me | solution 1 for BookProof.NavierStokesFlow.Carleman.tridiag_recursion_of_deficiency
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:06:15.756988+00:00
-- url     : https://prove2.me/submissions/8281d341-1fda-43bb-bf30-ab45bf41a7f3

-- Generated from ChapterNavierStokesCarleman.lean — solution of BookProof.NavierStokesFlow.Carleman.tridiag_recursion_of_deficiency
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Theorems.Thm_BookProof_NavierStokesFlow_Carleman_tridiagOp_basis_zero
import Theorems.Thm_BookProof_NavierStokesFlow_Carleman_tridiagOp_basis_succ
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman



open scoped ENNReal



open LpNat DiagonalEsa FullEsa

set_option maxHeartbeats 1000000 in
theorem solution (c : ℕ → ℂ) (z : ℂ) (w : L2N)
    (hw : ∀ v : lpFiniteModes ℕ,
      (inner ℂ ((tridiagOp c v : lpFiniteModes ℕ) : L2N) w : ℂ)
        = inner ℂ ((v : lpFiniteModes ℕ) : L2N) (z • w)) :
    ∀ n, tridiagFun c ((w : L2N) : ℕ → ℂ) n = z * ((w : L2N) : ℕ → ℂ) n := by

  intro n
  cases n with
  | zero =>
    have h := hw (basis 0)
    rw [tridiagOp_basis_zero] at h
    rw [inner_smul_left, lp.inner_single_left] at h
    rw [show ((basis 0 : lpFiniteModes ℕ) : L2N) = lp.single 2 0 (1 : ℂ) from rfl,
      lp.inner_single_left] at h
    simpa [tridiagFun] using h
  | succ k =>
    have h := hw (basis (k + 1))
    rw [tridiagOp_basis_succ] at h
    rw [inner_add_left, inner_smul_left, inner_smul_left, lp.inner_single_left,
      lp.inner_single_left] at h
    rw [show ((basis (k + 1) : lpFiniteModes ℕ) : L2N) = lp.single 2 (k + 1) (1 : ℂ) from rfl,
      lp.inner_single_left] at h
    simp only [Complex.conj_conj, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at h
    simpa [tridiagFun, add_comm] using h
