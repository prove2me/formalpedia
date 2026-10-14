-- Prove2me | solution 1 for BookProof.NavierStokesFlow.Carleman.tridiagOp_not_bounded
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:23:10.713817+00:00
-- url     : https://prove2.me/submissions/db04076d-28b4-44ff-ab96-ec6b8c2a6356

-- Generated from ChapterNavierStokesCarleman.lean — solution of BookProof.NavierStokesFlow.Carleman.tridiagOp_not_bounded
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Theorems.Thm_BookProof_NavierStokesFlow_Carleman_tridiagOp_basis_succ
import Theorems.Thm_BookProof_NavierStokesFlow_DiagonalEsa_norm_basis
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman



open scoped ENNReal



open LpNat DiagonalEsa FullEsa

set_option maxHeartbeats 1000000 in
theorem solution (c : ℕ → ℂ) (hc : ∀ C : ℝ, ∃ n, C < ‖c n‖) :
    ¬ ∃ C : ℝ, ∀ f : lpFiniteModes ℕ, ‖tridiagOp c f‖ ≤ C * ‖f‖ := by

  rintro ⟨C, hC⟩
  obtain ⟨k, hk⟩ := hc C
  have hb := hC (basis (k + 1))
  rw [norm_basis, mul_one] at hb
  have hcoord : ‖(((tridiagOp c (basis (k + 1)) : lpFiniteModes ℕ) : L2N) : ℕ → ℂ) k‖ ≤
      ‖((tridiagOp c (basis (k + 1)) : lpFiniteModes ℕ) : L2N)‖ :=
    lp.norm_apply_le_norm (by norm_num) _ k
  have hval : (((tridiagOp c (basis (k + 1)) : lpFiniteModes ℕ) : L2N) : ℕ → ℂ) k = c k := by
    rw [tridiagOp_basis_succ]
    show (starRingEnd ℂ (c (k + 1)) • (Subtype.val (lp.single 2 (k + 2) 1) : ℕ → ℂ)) k
      + (c k • (Subtype.val (lp.single 2 k 1) : ℕ → ℂ)) k = c k
    simp only [Pi.smul_apply, lp.single]
    simp
  rw [hval] at hcoord
  have : ‖c k‖ ≤ C := le_trans hcoord hb
  exact absurd hk (not_lt.mpr this)
