-- Prove2me | solution 5 for EulerMascheroni.gamma_irrational
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-04T18:04:54.562981+00:00
-- url     : https://prove2.me/submissions/edc76de1-2e4f-47b2-ace6-c0fc7f5f1833
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Apery_irrational_of_eventually_exists_int_poly
import Theorems.Thm_Apery_tendsto_pow_mul_exp_neg_sq_of_pos
import Theorems.Thm_EulerMascheroni_Hankel_exists_int_poly_quadratic_decay

open Polynomial Filter Topology

theorem solution : Irrational Real.eulerMascheroniConstant := by
  obtain ⟨D, c, hc, h⟩ := EulerMascheroni.Hankel.exists_int_poly_quadratic_decay
  refine Apery.irrational_of_eventually_exists_int_poly _ (fun n => D * n)
    (fun n => Real.exp (-c * (n : ℝ) ^ 2)) ?_ ?_
  · intro b hb
    have ht := Apery.tendsto_pow_mul_exp_neg_sq_of_pos hc (b ^ D) (Nat.pow_pos hb)
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) ht
    have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    push_cast
    rw [← pow_mul]
    exact pow_le_pow_right₀ hb1 (by nlinarith [Nat.zero_le (D * n)])
  · filter_upwards [h] with n hn
    obtain ⟨Q, hdeg, hpos, hlt⟩ := hn
    exact ⟨Q, hdeg, hpos, hlt.le⟩
