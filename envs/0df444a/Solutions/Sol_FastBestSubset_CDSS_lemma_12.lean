-- Prove2me | solution 1 for FastBestSubset.CDSS.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:48:36.769684+00:00
-- url     : https://prove2.me/submissions/94ff1ac0-58a2-4ddc-94c1-df67dad42e54

import Mathlib
import Definitions.Def_FastBestSubset_CDSS_Setting
open Filter Topology

namespace Aux_FBS12
open FastBestSubset.CDSS

variable {n p : ℕ}

lemma sum_split (β : Fin p → ℝ) (j : Fin p) (g : Fin p → ℝ → ℝ) :
    ∑ i, g i (β i) = g j (β j) + ∑ i ∈ Finset.univ.erase j, g i (β i) :=
  (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm

lemma sum_upd (β : Fin p → ℝ) (j : Fin p) (g : Fin p → ℝ → ℝ) :
    ∑ i, g i (Function.update β j 0 i) = g j 0 + ∑ i ∈ Finset.univ.erase j, g i (β i) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), Function.update_self]
  congr 1
  exact Finset.sum_congr rfl (fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)])

lemma l0_upd (β : Fin p → ℝ) (j : Fin p) (hj : β j ≠ 0) :
    (l0 β : ℝ) = l0 (Function.update β j 0) + 1 := by
  unfold l0
  have h : Finset.univ.filter (fun i => Function.update β j 0 i ≠ 0) =
      (Finset.univ.filter (fun i => β i ≠ 0)).erase j := by
    ext i
    by_cases hij : i = j
    · subst hij; simp
    · simp [Function.update_of_ne hij, hij]
  rw [h, Finset.card_erase_of_mem (by simp [hj])]
  have : 1 ≤ (Finset.univ.filter (fun i => β i ≠ 0)).card :=
    Finset.card_pos.mpr ⟨j, by simp [hj]⟩
  push_cast [Nat.cast_sub this]
  ring

lemma F_diff (D : Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1) (β : Fin p → ℝ) (j : Fin p)
    (hj : β j ≠ 0) :
    F D β - F D (Function.update β j 0) =
      (1 + 2 * D.lam2) / 2 * β j ^ 2 - btilde D β j * β j + D.lam1 * |β j| + D.lam0 := by
  have hl0 := l0_upd β j hj
  have hA : ∀ r, ∑ i, D.X r i * β i = D.X r j * β j + ∑ i ∈ Finset.univ.erase j, D.X r i * β i :=
    fun r => sum_split β j (fun i x => D.X r i * x)
  have hA' : ∀ r, ∑ i, D.X r i * Function.update β j 0 i =
      ∑ i ∈ Finset.univ.erase j, D.X r i * β i := by
    intro r
    have := sum_upd β j (fun i x => D.X r i * x)
    simpa using this
  have hB : ∑ i, |β i| = |β j| + ∑ i ∈ Finset.univ.erase j, |β i| :=
    sum_split β j (fun _ x => |x|)
  have hB' : ∑ i, |Function.update β j 0 i| = ∑ i ∈ Finset.univ.erase j, |β i| := by
    have := sum_upd β j (fun _ x => |x|)
    simpa using this
  have hC : ∑ i, β i ^ 2 = β j ^ 2 + ∑ i ∈ Finset.univ.erase j, β i ^ 2 :=
    sum_split β j (fun _ x => x ^ 2)
  have hC' : ∑ i, Function.update β j 0 i ^ 2 = ∑ i ∈ Finset.univ.erase j, β i ^ 2 := by
    have := sum_upd β j (fun _ x => x ^ 2)
    simpa using this
  have hquad : (1 / 2) * ∑ r, (D.y r - ∑ i, D.X r i * β i) ^ 2 -
      (1 / 2) * ∑ r, (D.y r - ∑ i, D.X r i * Function.update β j 0 i) ^ 2 =
      (1 / 2) * β j ^ 2 - btilde D β j * β j := by
    simp only [hA, hA']
    unfold btilde
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    have e : ∀ r, (D.y r - (D.X r j * β j + ∑ i ∈ Finset.univ.erase j, D.X r i * β i)) ^ 2 -
        (D.y r - ∑ i ∈ Finset.univ.erase j, D.X r i * β i) ^ 2 =
        β j ^ 2 * D.X r j ^ 2 -
          2 * β j * ((D.y r - ∑ i ∈ Finset.univ.erase j, D.X r i * β i) * D.X r j) := by
      intro r; ring
    simp only [e]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hX j]
    ring
  unfold F f
  rw [hl0, hB, hB', hC, hC']
  linarith [hquad]

end Aux_FBS12

open FastBestSubset.CDSS in
theorem solution {n p : ℕ} [NeZero p] (D : Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1)
    (hlam0 : 0 < D.lam0) (hlam1 : 0 ≤ D.lam1) (hlam2 : 0 ≤ D.lam2)
    (C : ℕ) (hC : 0 < C) (β0 : Fin p → ℝ) (k : ℕ) (j : Fin p)
    (hj : iter D C β0 k j ≠ 0)
    (hnonspacer : (stateAt D C β0 k).pending = false)
    (hcoord : coord (stateAt D C β0 k) = j)
    (hzero : iter D C β0 (k + 1) j = 0) :
    (1 + 2 * D.lam2) / 2 * (|iter D C β0 k j| - Real.sqrt (2 * D.lam0 / (1 + 2 * D.lam2))) ^ 2 ≤
      F D (iter D C β0 k) - F D (iter D C β0 (k + 1)) := by
  set β := iter D C β0 k with hβ
  set b := btilde D β j with hb
  have hstep : iter D C β0 (k + 1) = Function.update β j (T b D.lam0 D.lam1 D.lam2) := by
    have h1 : iter D C β0 (k + 1) = (step D C (stateAt D C β0 k)).beta := by
      unfold iter stateAt
      rw [Function.iterate_succ_apply']
    rw [h1]
    unfold step
    simp only [hnonspacer, Bool.false_eq_true, if_false, hcoord]
    rfl
  have hT0 : T b D.lam0 D.lam1 D.lam2 = 0 := by
    have := hzero
    rw [hstep, Function.update_self] at this
    exact this
  rw [hstep, hT0]
  set c := 1 + 2 * D.lam2 with hc
  have hcpos : 0 < c := by linarith
  set s := Real.sqrt (2 * D.lam0 / c) with hs
  have hs2 : s ^ 2 = 2 * D.lam0 / c := Real.sq_sqrt (by positivity)
  have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  -- the threshold condition fails
  have hm : |b| - D.lam1 < c * s := by
    by_contra hge
    push_neg at hge
    have hcond : s ≤ (|b| - D.lam1) / c := by rw [le_div_iff₀ hcpos]; linarith
    unfold T at hT0
    rw [if_pos hcond] at hT0
    have hpos : 0 < |b| - D.lam1 := by nlinarith
    have hbne : b ≠ 0 := by
      intro h; rw [h, abs_zero] at hpos; linarith
    have hsign : Real.sign b ≠ 0 := by
      rcases lt_or_gt_of_ne hbne with h | h
      · rw [Real.sign_of_neg h]; norm_num
      · rw [Real.sign_of_pos h]; norm_num
    have : Real.sign b * (|b| - D.lam1) / c ≠ 0 :=
      div_ne_zero (mul_ne_zero hsign hpos.ne') hcpos.ne'
    exact this hT0
  rw [Aux_FBS12.F_diff D hX β j hj]
  set t := |β j| with ht
  have ht0 : 0 ≤ t := abs_nonneg _
  have hbb : -(b * β j) ≥ -(|b| * t) := by
    have := abs_mul b (β j)
    have := le_abs_self (b * β j)
    rw [ht]; nlinarith [abs_mul b (β j)]
  have hsq : β j ^ 2 = t ^ 2 := by rw [ht, sq_abs]
  have hlam0' : D.lam0 = c * s ^ 2 / 2 := by rw [hs2]; field_simp
  rw [hsq]
  have hmt : (|b| - D.lam1) * t ≤ c * s * t := mul_le_mul_of_nonneg_right hm.le ht0
  nlinarith
