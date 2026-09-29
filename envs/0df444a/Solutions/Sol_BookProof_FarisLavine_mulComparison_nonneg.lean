-- Prove2me | solution 1 for BookProof.FarisLavine.mulComparison_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:43:14.162539+00:00
-- url     : https://prove2.me/submissions/08a8346b-6a57-4fb3-b51b-733a87a417c3

-- Generated from ChapterFarisLavine.lean — solution of BookProof.FarisLavine.mulComparison_nonneg
import Mathlib
import Definitions.Def_ChapterFarisLavine
import Theorems.Thm_BookProof_FarisLavine_conj_mul_ofReal
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Theorems.Thm_BookProof_FarisLavine_mulSymbolOp_coe
open BookProof.FarisLavine





variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}




open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat




open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem solution (lam : ℕ → ℝ) (x : mulSymbolDomain lam) :
    0 ≤ quadForm (mulComparison lam) x := by

  rw [quadForm, lp.inner_eq_tsum, Complex.re_tsum (lp.summable_inner _ _)]
  refine tsum_nonneg fun n => ?_
  have hterm : (inner ℂ (((x : L2Nat) : ℕ → ℂ) n)
      (((mulComparison lam x : L2Nat) : ℕ → ℂ) n) : ℂ)
      = ((|lam n| * Complex.normSq (((x : L2Nat) : ℕ → ℂ) n) : ℝ) : ℂ) := by
    simpa only [mulComparison, mulSymbolOp_coe, mulSymbolFun, RCLike.inner_apply] using
      conj_mul_ofReal (|lam n|) (((x : L2Nat) : ℕ → ℂ) n)
  rw [hterm, Complex.ofReal_re]
  exact mul_nonneg (abs_nonneg _) (Complex.normSq_nonneg _)
