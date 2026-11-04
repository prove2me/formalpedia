-- Prove2me | solution 1 for BookProof.CarlemanUnboundedHop.ladderRec_of_deficiency
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-03T21:16:54.42013+00:00
-- url     : https://prove2.me/submissions/94b66627-e680-49f4-a85e-950dc091746b

-- Generated from ChapterCarlemanUnboundedHop.lean — solution of BookProof.CarlemanUnboundedHop.ladderRec_of_deficiency
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
import Theorems.Thm_BookProof_CarlemanUnboundedHop_summable_normSq_lp
import Theorems.Thm_BookProof_CarlemanUnboundedHop_row_summable
import Definitions.Def_ChapterKernelBound
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.CarlemanUnboundedHop




open Finset
open BookProof.KernelBound
open BookProof.NavierStokesFlow.DiagonalEsa
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

set_option maxHeartbeats 1000000 in

theorem solution {a : ℕ → ℕ → ℂ} (hk : IsL2Kernel a) {z : ℂ} {w : L2N}
    (hw : ∀ v : lpFiniteModes ℕ, (inner ℂ (kernelOp hk v) (w : L2N) : ℂ)
        = z * inner ℂ (v : L2N) (w : L2N)) :
    LadderRecInf a ((w : ℕ → ℂ)) z := by
  classical
  have hw2 := summable_normSq_lp w
  have hrow : ∀ k : ℕ, Summable fun n : ℕ => a k n * (w : ℕ → ℂ) n := by
    intro k
    refine Summable.of_norm ?_
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (((row_summable hk k).add hw2).mul_left (1 / 2))
    rw [norm_mul]
    nlinarith [sq_nonneg (‖a k n‖ - ‖(w : ℕ → ℂ) n‖), norm_nonneg (a k n),
      norm_nonneg ((w : ℕ → ℂ) n)]
  refine ⟨hrow, fun k => ?_⟩
  -- test against `e_k`
  set v : lpFiniteModes ℕ := ⟨lp.single 2 k (1 : ℂ), lpSingle_mem_lpFiniteModes k 1⟩ with hv
  have hvcoe : ∀ j, ((v : L2N) : ℕ → ℂ) j = if j = k then (1 : ℂ) else 0 := by
    intro j; simp [hv, lp.single_apply, Pi.single_apply]
  have hTv : ∀ n, ((kernelOp hk v : L2N) : ℕ → ℂ) n = a n k := by
    intro n
    rw [kernelOp_coe, kernelFun]
    rw [tsum_eq_single k (by
      intro b hb
      rw [hvcoe b, if_neg hb]
      ring)]
    rw [hvcoe k, if_pos rfl]
    ring
  have hrhs : (inner ℂ (v : L2N) (w : L2N) : ℂ) = (w : ℕ → ℂ) k := by
    rw [lp.inner_eq_tsum]
    rw [tsum_eq_single k (by
      intro b hb
      simp [RCLike.inner_apply, hvcoe b, if_neg hb])]
    simp [RCLike.inner_apply, hvcoe k]
  have hlhs : (inner ℂ (kernelOp hk v : L2N) (w : L2N) : ℂ)
      = ∑' n : ℕ, a k n * (w : ℕ → ℂ) n := by
    rw [lp.inner_eq_tsum]
    refine tsum_congr fun n => ?_
    rw [RCLike.inner_apply, hTv n, hk.herm n k]
    ring
  have := hw v
  rw [hlhs, hrhs] at this
  exact this
