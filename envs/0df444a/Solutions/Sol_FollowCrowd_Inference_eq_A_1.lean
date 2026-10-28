-- Prove2me | solution 1 for FollowCrowd.Inference.eq_A_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:06:55.307155+00:00
-- url     : https://prove2.me/submissions/cd3dd525-0757-4203-a345-d7a906f8db25

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
    (∀ mu ∈ ({P.muH, P.muL} : Set ℝ),
      (∀ n, 0 ≤ stat P mu p n) ∧ ∑ n ∈ Finset.range (Nbar P + 1), stat P mu p n = 1) ∧
    ∀ n ≤ Nbar P, 0 < ∏ i ∈ Finset.range n, p i →
      theta P p n = P.γ * stat P P.muH p n /
        (P.γ * stat P P.muH p n + (1 - P.γ) * stat P P.muL p n) := by
  obtain ⟨hL, hLH, hg0, hg1, hlam, hC, hR⟩ := hP
  have hH : 0 < P.muH := lt_trans hL hLH
  refine ⟨fun mu hmu => ?_, fun n hn hprod => ?_⟩
  · have hmu0 : 0 < mu := by
      rcases hmu with h | h
      · rw [h]; exact hH
      · rw [Set.mem_singleton_iff.1 h]; exact hL
    have hZ := Z_pos P hmu0 hlam hp
    refine ⟨fun n => ?_, ?_⟩
    · unfold stat
      split_ifs
      · exact div_nonneg (weight_nonneg P hmu0 hlam hp n) hZ.le
      · exact le_rfl
    · rw [Finset.sum_congr rfl (fun n hn => by
        rw [stat, if_pos (by have := Finset.mem_range.1 hn; omega)])]
      rw [← Finset.sum_div, div_self hZ.ne']
  · have hZH := Z_pos P hH hlam hp
    have hZL := Z_pos P hL hlam hp
    have hrH : 0 < rho P P.muH := div_pos hlam hH
    have hrL : 0 < rho P P.muL := div_pos hlam hL
    set c := rho P P.muH ^ n * ∏ i ∈ Finset.range n, p i with hc
    have hcpos : 0 < c := mul_pos (pow_pos hrH n) hprod
    have e1 : P.γ * stat P P.muH p n = c * (P.γ * stat P P.muH p 0) := by
      rw [stat_eq P _ p hn, stat0]; ring
    have e2 : (1 - P.γ) * stat P P.muL p n =
        c * ((1 - P.γ) * stat P P.muL p 0 * (rho P P.muL / rho P P.muH) ^ n) := by
      rw [stat_eq P _ p hn, stat0, div_pow, hc]
      field_simp
    rw [e1, e2, ← mul_add, mul_div_mul_left _ _ hcpos.ne']
    rfl
