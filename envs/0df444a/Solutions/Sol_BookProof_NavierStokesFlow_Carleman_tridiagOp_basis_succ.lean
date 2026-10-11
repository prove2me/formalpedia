-- Prove2me | solution 1 for BookProof.NavierStokesFlow.Carleman.tridiagOp_basis_succ
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:06:00.784596+00:00
-- url     : https://prove2.me/submissions/b0827de0-f7f4-4160-8342-df32a6abdd97

-- Generated from ChapterNavierStokesCarleman.lean — solution of BookProof.NavierStokesFlow.Carleman.tridiagOp_basis_succ
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman



open scoped ENNReal



open LpNat DiagonalEsa FullEsa

set_option maxHeartbeats 1000000 in
theorem solution (c : ℕ → ℂ) (k : ℕ) :
    ((tridiagOp c (basis (k + 1)) : lpFiniteModes ℕ) : L2N)
      = (starRingEnd ℂ (c (k + 1))) • lp.single 2 (k + 2) (1 : ℂ)
        + (c k) • lp.single 2 k (1 : ℂ) := by

  ext m
  cases m with
  | zero =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp [tridiagOp, basis, tridiagFun, lp.single_apply, lp.coeFn_add]
      show c 0 = starRingEnd ℂ (c 1) * (0 : ℂ) + c 0 * (1 : ℂ)
      ring
    · have hk1 : (0 : ℕ) ≠ k := by omega
      have hk0 : ¬ (k = 0) := by omega
      have hk2 : (0 : ℕ) ≠ k + 2 := by omega
      simp [tridiagOp, basis, tridiagFun, lp.single_apply, lp.coeFn_add, hk1, hk0]
      show (0 : ℂ) = (starRingEnd ℂ (c (k + 1)) • (Subtype.val (lp.single 2 (k + 2) 1) : ℕ → ℂ)) 0
        + (c k • (Subtype.val (lp.single 2 k 1) : ℕ → ℂ)) 0
      simp only [Pi.smul_apply, lp.single]
      simp [Pi.single_eq_of_ne, Pi.single_eq_same, hk1, hk2]
  | succ j =>
    by_cases hjk : j = k + 1
    · subst hjk
      have hne : ¬ (k + 1 + 1 = k) := by omega
      simp [tridiagOp, basis, tridiagFun, lp.single_apply, lp.coeFn_add, hne]
      show starRingEnd ℂ (c (k + 1)) =
        (starRingEnd ℂ (c (k + 1)) • (Subtype.val (lp.single 2 (k + 2) 1) : ℕ → ℂ)) (k + 1 + 1)
          + (c k • (Subtype.val (lp.single 2 k 1) : ℕ → ℂ)) (k + 1 + 1)
      simp only [Pi.smul_apply, lp.single]
      rw [Pi.single_eq_of_ne hne]
      simp
    · by_cases hjk2 : j + 1 = k
      · subst hjk2
        simp [tridiagOp, basis, tridiagFun, lp.single_apply, lp.coeFn_add, hjk]
        show c (j + 1) =
          (starRingEnd ℂ (c (j + 1 + 1)) • (Subtype.val (lp.single 2 (j + 1 + 2) 1) : ℕ → ℂ)) (j + 1)
            + (c (j + 1) • (Subtype.val (lp.single 2 (j + 1) 1) : ℕ → ℂ)) (j + 1)
        simp only [Pi.smul_apply, lp.single]
        simp
      · have h1 : j ≠ k + 1 := hjk
        have h2 : j + 2 ≠ k + 1 := by omega
        have h4 : j + 1 ≠ k := by omega
        have h5 : j + 1 ≠ k + 2 := by omega
        simp [tridiagOp, basis, tridiagFun, lp.single_apply, lp.coeFn_add, h1, h2, h4]
        show (0 : ℂ) =
          (starRingEnd ℂ (c (k + 1)) • (Subtype.val (lp.single 2 (k + 2) 1) : ℕ → ℂ)) (j + 1)
            + (c k • (Subtype.val (lp.single 2 k 1) : ℕ → ℂ)) (j + 1)
        simp only [Pi.smul_apply, lp.single]
        rw [Pi.single_eq_of_ne h5, Pi.single_eq_of_ne h4]
        simp
