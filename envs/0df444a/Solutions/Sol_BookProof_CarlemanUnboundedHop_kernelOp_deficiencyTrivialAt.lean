-- Prove2me | solution 1 for BookProof.CarlemanUnboundedHop.kernelOp_deficiencyTrivialAt
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T05:54:53.296604+00:00
-- url     : https://prove2.me/submissions/8654787a-a06d-4b30-a88e-826a8fd327d0

import Mathlib
import Theorems.Thm_BookProof_CarlemanUnboundedHop_ladder_eq_zero_of_carleman
import Theorems.Thm_BookProof_CarlemanUnboundedHop_row_summable
import Theorems.Thm_BookProof_CarlemanUnboundedHop_summable_normSq_lp

import Definitions.Def_ChapterCarlemanUnboundedHop
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterKernelBound
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.KernelBound
open BookProof.CarlemanUnboundedHop



open Finset
open BookProof.FarisLavine
open BookProof.NavierStokesFlow

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

theorem kdt_summable_mul {f g : ℕ → ℂ} (hf : Summable fun n => ‖f n‖ ^ 2)
    (hg : Summable fun n => ‖g n‖ ^ 2) : Summable fun n => f n * g n := by
  refine Summable.of_norm_bounded ((hf.add hg).div_const 2) fun n => ?_
  rw [norm_mul]
  nlinarith [sq_nonneg (‖f n‖ - ‖g n‖)]

theorem solution {a : ℕ → ℕ → ℂ} {A θ Θ : ℕ → ℝ} (hk : IsL2Kernel a)
    (hθ0 : ∀ r, 0 ≤ θ r) (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j))
    (hΘsum : Summable Θ) (hApos : ∀ n, 0 < A n) (hAmono : Monotone A)
    (hbd : ∀ n k, n < k → ‖a n k‖ ≤ A n * θ (k - n))
    (hcar : ¬ Summable fun n => (A n)⁻¹) {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (lpFiniteModes ℕ) (kernelOp hk) z := by
  classical
  intro w hw
  set u : ℕ → ℂ := (w : ℕ → ℂ) with hu
  have hu2 : Summable fun n => ‖u n‖ ^ 2 := BookProof.CarlemanUnboundedHop.summable_normSq_lp w
  have hrow : ∀ m, Summable fun k => a m k * u k := fun m =>
    kdt_summable_mul (BookProof.CarlemanUnboundedHop.row_summable hk m) hu2
  have heqn : ∀ m, ∑' k, a m k * u k = z * u m := by
    intro m
    have h := hw ⟨lp.single 2 m (1 : ℂ), lpSingle_mem_lpFiniteModes m 1⟩
    have hcol : ((kernelOp hk ⟨lp.single 2 m (1 : ℂ), lpSingle_mem_lpFiniteModes m 1⟩ : lp (fun _ : ℕ => ℂ) 2) : ℕ → ℂ)
        = fun n => a n m := by
      rw [kernelOp_coe]
      funext n
      have hM : ∀ k, m + 1 ≤ k → ((lp.single 2 m (1 : ℂ) : lp (fun _ : ℕ => ℂ) 2) : ℕ → ℂ) k = 0 := by
        intro k hk'
        rw [lp.single_apply, Pi.single_apply, if_neg (by omega)]
      rw [kernelFun_eq_sum a hM n, Finset.sum_eq_single m]
      · rw [lp.single_apply, Pi.single_eq_same, mul_one]
      · intro k _ hkm
        rw [lp.single_apply, Pi.single_apply, if_neg hkm, mul_zero]
      · intro hm; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self m)) hm
    change (inner ℂ (kernelOp hk ⟨lp.single 2 m (1 : ℂ), lpSingle_mem_lpFiniteModes m 1⟩ : lp (fun _ : ℕ => ℂ) 2) w : ℂ)
      = z * inner ℂ (lp.single 2 m (1 : ℂ) : lp (fun _ : ℕ => ℂ) 2) w at h
    rw [lp.inner_single_left, lp.inner_eq_tsum, hcol] at h
    simp only [RCLike.inner_apply, map_one, one_mul] at h
    simp only [mul_one] at h
    rw [hu, ← h]
    refine tsum_congr fun k => ?_
    rw [hk.herm m k, Complex.conj_conj, mul_comm]
  have hzero := BookProof.CarlemanUnboundedHop.ladder_eq_zero_of_carleman hz hk.herm
    ⟨hrow, heqn⟩ hu2 hθ0 hΘ hΘsum hApos hAmono hbd hcar
  exact lp.ext (funext fun n => by simpa [hu] using hzero n)
