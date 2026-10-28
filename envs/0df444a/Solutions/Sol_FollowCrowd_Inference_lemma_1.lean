-- Prove2me | solution 1 for FollowCrowd.Inference.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:10:11.520078+00:00
-- url     : https://prove2.me/submissions/4f28ddc2-21ae-4edb-a213-96ca7a34ccde

import Mathlib
import Definitions.Def_FollowCrowd_Inference_Model

namespace Aux_FollowW31
open FollowCrowd.Inference

lemma weight_nonneg (P : Params) {mu : ℝ} (hmu : 0 < mu) (hlam : 0 < P.lam) {p : ℕ → ℝ}
    (hp : IsJoinVec p) (n : ℕ) : 0 ≤ weight P mu p n :=
  mul_nonneg (pow_nonneg (div_pos hlam hmu).le _) (Finset.prod_nonneg fun i _ => (hp.2 i).1)

lemma weight_zero (P : Params) (mu : ℝ) (p : ℕ → ℝ) : weight P mu p 0 = 1 := by
  simp [weight]

lemma Z_pos (P : Params) {mu : ℝ} (hmu : 0 < mu) (hlam : 0 < P.lam) {p : ℕ → ℝ}
    (hp : IsJoinVec p) : 0 < ∑ j ∈ Finset.range (Nbar P + 1), weight P mu p j := by
  have := Finset.single_le_sum (f := weight P mu p) (fun i _ => weight_nonneg P hmu hlam hp i)
    (Finset.mem_range.2 (Nat.succ_pos (Nbar P)))
  rw [weight_zero] at this
  linarith

lemma stat_eq (P : Params) (mu : ℝ) (p : ℕ → ℝ) {n : ℕ} (hn : n ≤ Nbar P) :
    stat P mu p n = rho P mu ^ n * (∏ i ∈ Finset.range n, p i) /
      ∑ j ∈ Finset.range (Nbar P + 1), weight P mu p j := by
  rw [stat, if_pos hn, weight]

lemma stat0 (P : Params) (mu : ℝ) (p : ℕ → ℝ) :
    stat P mu p 0 = 1 / ∑ j ∈ Finset.range (Nbar P + 1), weight P mu p j := by
  rw [stat_eq P mu p (Nat.zero_le _)]; simp

end Aux_FollowW31

open FollowCrowd.Inference Aux_FollowW31 in
theorem solution (P : Params) (hP : P.Standing) (p : ℕ → ℝ) (hp : IsJoinVec p) :
    StrictAnti (theta P p) ∧ StrictAnti (util P p) := by
  obtain ⟨hL, hLH, hg0, hg1, hlam, hC, hR⟩ := hP
  have hH : 0 < P.muH := lt_trans hL hLH
  have hZH := Z_pos P hH hlam hp
  have hZL := Z_pos P hL hlam hp
  set X := P.γ * stat P P.muH p 0 with hX
  set Y := (1 - P.γ) * stat P P.muL p 0 with hY
  set r := rho P P.muL / rho P P.muH with hr
  have hXp : 0 < X := by rw [hX, stat0]; exact mul_pos hg0 (one_div_pos.2 hZH)
  have hYp : 0 < Y := by rw [hY, stat0]; exact mul_pos (by linarith) (one_div_pos.2 hZL)
  have hr1 : 1 < r := by
    rw [hr, one_lt_div (show 0 < rho P P.muH from div_pos hlam hH)]
    show P.lam / P.muH < P.lam / P.muL
    exact div_lt_div_of_pos_left hlam hL hLH
  have hrpos : 0 < r := by linarith
  have hth : ∀ n, theta P p n = X / (X + Y * r ^ n) := fun n => by
    rw [theta, hX, hY, hr, mul_assoc]
  have hthS : ∀ n, theta P p (n + 1) < theta P p n := by
    intro n
    rw [hth, hth]
    apply div_lt_div_of_pos_left hXp (add_pos hXp (mul_pos hYp (pow_pos hrpos n)))
    have := pow_lt_pow_right₀ hr1 (by omega : n < n + 1)
    nlinarith [mul_lt_mul_of_pos_left this hYp]
  have hth01 : ∀ n, 0 < theta P p n ∧ theta P p n < 1 := by
    intro n
    rw [hth]
    have hpos : 0 < Y * r ^ n := mul_pos hYp (pow_pos hrpos n)
    exact ⟨div_pos hXp (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩
  have hinv : 1 / P.muH < 1 / P.muL := one_div_lt_one_div_of_lt hL hLH
  have hms : ∀ n, meanSojourn P (theta P p n) < meanSojourn P (theta P p (n + 1)) := by
    intro n
    have h1 := hthS n
    unfold meanSojourn
    have e : ∀ t : ℝ, t / P.muH + (1 - t) / P.muL = 1 / P.muL - t * (1 / P.muL - 1 / P.muH) :=
      fun t => by ring
    rw [e, e]
    nlinarith [mul_lt_mul_of_pos_right h1 (sub_pos.2 hinv)]
  have hmpos : ∀ n, 0 < meanSojourn P (theta P p n) := by
    intro n
    obtain ⟨a, b⟩ := hth01 n
    unfold meanSojourn
    have := div_pos a hH
    have := div_pos (sub_pos.2 b) hL
    linarith
  refine ⟨strictAnti_nat_of_succ_lt hthS, strictAnti_nat_of_succ_lt fun n => ?_⟩
  unfold util
  have h1 := hms n
  have h2 := hmpos n
  push_cast
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have : ((n:ℝ) + 1) * meanSojourn P (theta P p n) <
      ((n:ℝ) + 1 + 1) * meanSojourn P (theta P p (n + 1)) := by nlinarith
  nlinarith [mul_lt_mul_of_pos_left this hC]
