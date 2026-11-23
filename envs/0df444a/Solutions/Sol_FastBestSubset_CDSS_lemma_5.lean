-- Prove2me | solution 1 for FastBestSubset.CDSS.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:18:13.116273+00:00
-- url     : https://prove2.me/submissions/e9631ab5-7f67-41a6-b702-abbec3a0e67e

import Mathlib
import Definitions.Def_FastBestSubset_CDSS_Setting

set_option autoImplicit false

open Filter Topology FastBestSubset.CDSS

namespace FastBestSubset.CDSS.Lemma5Proof

theorem T_min_gScalar (a lam0 lam1 lam2 : ℝ) (h0 : 0 ≤ lam0) (h1 : 0 ≤ lam1) (h2 : 0 ≤ lam2)
    (v : ℝ) :
    gScalar a lam0 lam1 lam2 (T a lam0 lam1 lam2) ≤ gScalar a lam0 lam1 lam2 v := by
  set α : ℝ := 1 + 2 * lam2 with hαdef
  have hα : 0 < α := by linarith
  have hg0 : gScalar a lam0 lam1 lam2 0 = a ^ 2 / (2 * α) := by
    unfold gScalar
    rw [← hαdef]
    simp only [zero_sub, neg_sq, abs_zero, mul_zero, add_zero, ne_eq, not_true_eq_false, ite_false]
    field_simp
  have hg_lb : ∀ w : ℝ, w ≠ 0 →
      a ^ 2 / (2 * α) + α / 2 * (|w| - (|a| - lam1) / α) ^ 2 +
        lam0 - (|a| - lam1) ^ 2 / (2 * α) ≤ gScalar a lam0 lam1 lam2 w := by
    intro w hw
    unfold gScalar
    rw [← hαdef, if_pos hw, mul_one]
    have haw : a * w ≤ |a| * |w| := by rw [← abs_mul]; exact le_abs_self _
    have hw2 : w ^ 2 = |w| ^ 2 := (sq_abs w).symm
    have hexp1 : α / 2 * (w - a / α) ^ 2 + lam1 * |w| + lam0 =
        a ^ 2 / (2 * α) + α / 2 * w ^ 2 - a * w + lam1 * |w| + lam0 := by
      field_simp; ring
    have hexp2 : a ^ 2 / (2 * α) + α / 2 * (|w| - (|a| - lam1) / α) ^ 2 +
          lam0 - (|a| - lam1) ^ 2 / (2 * α) =
        a ^ 2 / (2 * α) + α / 2 * |w| ^ 2 - |a| * |w| + lam1 * |w| + lam0 := by
      field_simp; ring
    rw [hexp1, hexp2, hw2]
    linarith
  have hg_nonneg0 : ∀ w : ℝ, |a| - lam1 ≤ 0 →
      gScalar a lam0 lam1 lam2 0 ≤ gScalar a lam0 lam1 lam2 w := by
    intro w hle
    by_cases hw : w = 0
    · rw [hw]
    · rw [hg0]
      unfold gScalar
      rw [← hαdef, if_pos hw, mul_one]
      have haw : a * w ≤ |a| * |w| := by rw [← abs_mul]; exact le_abs_self _
      have hexp1 : α / 2 * (w - a / α) ^ 2 + lam1 * |w| + lam0 =
          a ^ 2 / (2 * α) + α / 2 * w ^ 2 + (lam1 * |w| - a * w) + lam0 := by
        field_simp; ring
      rw [hexp1]
      have hterm1 : 0 ≤ α / 2 * w ^ 2 := by positivity
      have hterm2 : 0 ≤ lam1 * |w| - a * w := by
        have : |a| * |w| ≤ lam1 * |w| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg w)
        linarith
      linarith
  unfold T
  rw [← hαdef]
  split_ifs with hcond
  · have hnonneg_num : 0 ≤ |a| - lam1 := by
      have : 0 ≤ (|a| - lam1) / α := le_trans (Real.sqrt_nonneg _) hcond
      have hmul := (le_div_iff₀ hα).mp this
      linarith
    by_cases hzero : |a| - lam1 = 0
    · rw [hzero, mul_zero, zero_div]
      exact hg_nonneg0 v (by linarith)
    · have hpos_num : 0 < |a| - lam1 := lt_of_le_of_ne hnonneg_num (Ne.symm hzero)
      have ha_ne : a ≠ 0 := by
        intro ha0; rw [ha0, abs_zero] at hpos_num; linarith
      have hsq_cond : 2 * lam0 / α ≤ ((|a| - lam1) / α) ^ 2 := by
        have h1 := mul_self_le_mul_self (Real.sqrt_nonneg _) hcond
        rw [Real.mul_self_sqrt (by positivity), ← sq] at h1
        exact h1
      have hlam0_le : lam0 ≤ (|a| - lam1) ^ 2 / (2 * α) := by
        rw [div_pow] at hsq_cond
        have hmul := mul_le_mul_of_nonneg_left hsq_cond (show 0 ≤ α ^ 2 / 2 by positivity)
        have e1 : α ^ 2 / 2 * (2 * lam0 / α) = α * lam0 := by field_simp
        have e2 : α ^ 2 / 2 * ((|a| - lam1) ^ 2 / α ^ 2) = (|a| - lam1) ^ 2 / 2 := by field_simp
        rw [e1, e2] at hmul
        rw [le_div_iff₀ (by positivity)]
        linarith
      set u := Real.sign a * (|a| - lam1) / α
      have hu_abs : |u| = (|a| - lam1) / α := by
        simp only [u]
        rcases lt_or_gt_of_ne ha_ne with hlt | hgt
        · rw [Real.sign_of_neg hlt, abs_div, abs_mul, abs_neg, abs_one, one_mul,
            abs_of_pos hpos_num, abs_of_pos hα]
        · rw [Real.sign_of_pos hgt, abs_div, abs_mul, abs_one, one_mul,
            abs_of_pos hpos_num, abs_of_pos hα]
      have hu_val : gScalar a lam0 lam1 lam2 u ≤
          a ^ 2 / (2 * α) + lam0 - (|a| - lam1) ^ 2 / (2 * α) := by
        unfold gScalar
        rw [← hαdef, hu_abs]
        have hite : (if u ≠ 0 then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
        have hmul_ite : lam0 * (if u ≠ 0 then (1 : ℝ) else 0) ≤ lam0 := by nlinarith
        have hquad : α / 2 * (u - a / α) ^ 2 + lam1 * ((|a| - lam1) / α) =
            a ^ 2 / (2 * α) - (|a| - lam1) ^ 2 / (2 * α) := by
          simp only [u]
          rcases lt_or_gt_of_ne ha_ne with hlt | hgt
          · rw [Real.sign_of_neg hlt, abs_of_neg hlt]; field_simp; ring
          · rw [Real.sign_of_pos hgt, abs_of_pos hgt]; field_simp; ring
        linarith
      by_cases hv0 : v = 0
      · rw [hv0, hg0]
        linarith
      · have hlb := hg_lb v hv0
        have hsq_nn : 0 ≤ α / 2 * (|v| - (|a| - lam1) / α) ^ 2 := by positivity
        linarith
  · push Not at hcond
    by_cases hnum : |a| - lam1 ≤ 0
    · exact hg_nonneg0 v hnum
    · push Not at hnum
      by_cases hv0 : v = 0
      · rw [hv0]
      · have hsq_lt : ((|a| - lam1) / α) ^ 2 < 2 * lam0 / α :=
          (Real.lt_sqrt (by positivity)).mp hcond
        have hlam0_gt : (|a| - lam1) ^ 2 / (2 * α) < lam0 := by
          rw [div_pow] at hsq_lt
          have hmul := mul_lt_mul_of_pos_left hsq_lt (show 0 < α ^ 2 / 2 by positivity)
          have e1 : α ^ 2 / 2 * (2 * lam0 / α) = α * lam0 := by field_simp
          have e2 : α ^ 2 / 2 * ((|a| - lam1) ^ 2 / α ^ 2) = (|a| - lam1) ^ 2 / 2 := by field_simp
          rw [e1, e2] at hmul
          rw [div_lt_iff₀ (by positivity)]
          linarith
        have hlb := hg_lb v hv0
        have hsq_nn : 0 ≤ α / 2 * (|v| - (|a| - lam1) / α) ^ 2 := by positivity
        rw [hg0]
        linarith

theorem f_coord_diff {n p : ℕ} (D : Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1)
    (hlam2 : 0 ≤ D.lam2) (b : Fin p → ℝ) (i : Fin p) (u : ℝ) :
    f D (Function.update b i u) - f D b =
      gScalar (btilde D b i) 0 D.lam1 D.lam2 u -
        gScalar (btilde D b i) 0 D.lam1 D.lam2 (b i) := by
  have hden : (1 + 2 * D.lam2 : ℝ) ≠ 0 := by linarith
  have hres_diff : (1 / 2 : ℝ) * ∑ r, (D.y r - ∑ j, D.X r j * Function.update b i u j) ^ 2 -
      (1 / 2 : ℝ) * ∑ r, (D.y r - ∑ j, D.X r j * b j) ^ 2 =
      (1 / 2 : ℝ) * (u ^ 2 - b i ^ 2) - btilde D b i * (u - b i) := by
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    have hrow : ∀ r : Fin n,
        (D.y r - ∑ j, D.X r j * Function.update b i u j) ^ 2 -
          (D.y r - ∑ j, D.X r j * b j) ^ 2 =
          D.X r i ^ 2 * (u ^ 2 - b i ^ 2) -
            2 * ((D.y r - ∑ j ∈ Finset.univ.erase i, D.X r j * b j) * D.X r i) * (u - b i) := by
      intro r
      have s1 : ∑ j, D.X r j * Function.update b i u j =
          D.X r i * u + ∑ j ∈ Finset.univ.erase i, D.X r j * b j := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self]
        congr 1
        exact Finset.sum_congr rfl fun j hj => by
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      have s2 : ∑ j, D.X r j * b j =
          D.X r i * b i + ∑ j ∈ Finset.univ.erase i, D.X r j * b j :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
      rw [s1, s2]
      ring
    rw [Finset.sum_congr rfl fun r _ => hrow r, Finset.sum_sub_distrib, ← Finset.sum_mul,
      hX i, one_mul]
    have hbt : ∑ r, 2 * ((D.y r - ∑ j ∈ Finset.univ.erase i, D.X r j * b j) * D.X r i) * (u - b i) =
        2 * btilde D b i * (u - b i) := by
      unfold btilde
      rw [Finset.mul_sum, Finset.sum_mul]
      try exact Finset.sum_congr rfl fun r _ => by ring
    rw [hbt]
    ring
  have hl1_diff : ∑ j, |Function.update b i u j| - ∑ j, |b j| = |u| - |b i| := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [hji]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hl2_diff : ∑ j, (Function.update b i u j) ^ 2 - ∑ j, b j ^ 2 = u ^ 2 - b i ^ 2 := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [hji]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hdiff_LHS : f D (Function.update b i u) - f D b =
      ((1 / 2 : ℝ) * ∑ r, (D.y r - ∑ j, D.X r j * Function.update b i u j) ^ 2 -
        (1 / 2 : ℝ) * ∑ r, (D.y r - ∑ j, D.X r j * b j) ^ 2) +
      D.lam1 * (∑ j, |Function.update b i u j| - ∑ j, |b j|) +
      D.lam2 * (∑ j, (Function.update b i u j) ^ 2 - ∑ j, b j ^ 2) := by
    unfold f; ring
  rw [hdiff_LHS, hres_diff, hl1_diff, hl2_diff]
  unfold gScalar
  simp only [zero_mul, add_zero]
  field_simp
  ring

theorem l0_coord_diff {p : ℕ} (b : Fin p → ℝ) (i : Fin p) (u : ℝ) :
    (l0 (Function.update b i u) : ℝ) - (l0 b : ℝ) =
      (if u ≠ 0 then 1 else 0) - (if b i ≠ 0 then 1 else 0) := by
  unfold l0
  rw [← Finset.sum_boole, ← Finset.sum_boole, ← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · simp
  · intro j _ hji; simp [hji]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem F_coord_diff {n p : ℕ} (D : Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1)
    (hlam2 : 0 ≤ D.lam2) (b : Fin p → ℝ) (i : Fin p) (u : ℝ) :
    F D (Function.update b i u) - F D b =
      gScalar (btilde D b i) D.lam0 D.lam1 D.lam2 u -
        gScalar (btilde D b i) D.lam0 D.lam1 D.lam2 (b i) := by
  have hF : F D (Function.update b i u) - F D b =
      (f D (Function.update b i u) - f D b) +
        D.lam0 * ((l0 (Function.update b i u) : ℝ) - (l0 b : ℝ)) := by
    unfold F; ring
  rw [hF, f_coord_diff D hX hlam2 b i u, l0_coord_diff b i u]
  unfold gScalar
  ring

theorem spacer_foldl_le {n p : ℕ} (D : Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1)
    (hlam0 : 0 < D.lam0) (hlam1 : 0 ≤ D.lam1) (hlam2 : 0 ≤ D.lam2)
    (β : Fin p → ℝ) :
    ∀ (L : List (Fin p)) (b : Fin p → ℝ), L.Nodup → (∀ j ∈ L, b j = β j) →
      F D (L.foldl (fun acc i =>
        if β i ≠ 0 then Function.update acc i (T (btilde D acc i) 0 D.lam1 D.lam2) else acc) b) ≤
        F D b
  | [], b, _, _ => le_rfl
  | i :: tl, b, hnd, hagree => by
    obtain ⟨hi_not_mem, hnd_tl⟩ := List.nodup_cons.mp hnd
    simp only [List.foldl_cons]
    by_cases hβi : β i ≠ 0
    · rw [if_pos hβi]
      set u := T (btilde D b i) 0 D.lam1 D.lam2
      let b' := Function.update b i u
      have hbi : b i ≠ 0 := by rw [hagree i List.mem_cons_self]; exact hβi
      have hf_le : f D b' ≤ f D b := by
        have h1 := f_coord_diff D hX hlam2 b i u
        have h2 := T_min_gScalar (btilde D b i) 0 D.lam1 D.lam2 le_rfl hlam1 hlam2 (b i)
        linarith
      have hl0_le : (l0 b' : ℝ) ≤ (l0 b : ℝ) := by
        change (l0 (Function.update b i u) : ℝ) ≤ (l0 b : ℝ)
        have h1 := l0_coord_diff b i u
        have hb1 : (if b i ≠ 0 then (1 : ℝ) else 0) = 1 := if_pos hbi
        have hu1 : (if u ≠ 0 then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
        linarith
      have hF_step : F D b' ≤ F D b := by
        unfold F
        have := mul_le_mul_of_nonneg_left hl0_le hlam0.le
        linarith
      have hagree' : ∀ j ∈ tl, b' j = β j := by
        intro j hj
        have hji : j ≠ i := fun h => hi_not_mem (h ▸ hj)
        simp only [b', Function.update_of_ne hji]
        exact hagree j (List.mem_cons_of_mem i hj)
      exact (spacer_foldl_le D hX hlam0 hlam1 hlam2 β tl b' hnd_tl hagree').trans hF_step
    · rw [if_neg hβi]
      exact spacer_foldl_le D hX hlam0 hlam1 hlam2 β tl b hnd_tl
        (fun j hj => hagree j (List.mem_cons_of_mem i hj))

end FastBestSubset.CDSS.Lemma5Proof

open FastBestSubset.CDSS.Lemma5Proof in
theorem solution {n p : ℕ} [NeZero p] (D : Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1)
    (hlam0 : 0 < D.lam0) (hlam1 : 0 ≤ D.lam1) (hlam2 : 0 ≤ D.lam2)
    (C : ℕ) (_hC : 0 < C) (β0 : Fin p → ℝ) :
    (∀ k, F D (iter D C β0 (k + 1)) ≤ F D (iter D C β0 k)) ∧
      ∃ Fstar : ℝ, 0 ≤ Fstar ∧ Tendsto (fun k => F D (iter D C β0 k)) atTop (𝓝 Fstar) := by
  have hF_nonneg : ∀ β : Fin p → ℝ, 0 ≤ F D β := by
    intro β
    unfold F f
    have h1 : 0 ≤ (1 / 2 : ℝ) * ∑ r, (D.y r - ∑ j, D.X r j * β j) ^ 2 :=
      mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have h2 : 0 ≤ D.lam1 * ∑ j, |β j| :=
      mul_nonneg hlam1 (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    have h3 : 0 ≤ D.lam2 * ∑ j, β j ^ 2 :=
      mul_nonneg hlam2 (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have h4 : 0 ≤ D.lam0 * (l0 β : ℝ) := mul_nonneg hlam0.le (Nat.cast_nonneg _)
    linarith
  have hdescent : ∀ k, F D (iter D C β0 (k + 1)) ≤ F D (iter D C β0 k) := by
    intro k
    unfold iter stateAt
    rw [Function.iterate_succ_apply']
    set s := (step D C)^[k] (init β0)
    unfold step
    split_ifs with hp
    · dsimp only
      unfold spacer
      exact spacer_foldl_le D hX hlam0 hlam1 hlam2 s.beta (List.finRange p) s.beta
        (List.nodup_finRange p) (fun _ _ => rfl)
    · dsimp only
      set i := coord s
      set u := T (btilde D s.beta i) D.lam0 D.lam1 D.lam2
      have h1 := F_coord_diff D hX hlam2 s.beta i u
      have h2 := T_min_gScalar (btilde D s.beta i) D.lam0 D.lam1 D.lam2 hlam0.le hlam1 hlam2 (s.beta i)
      linarith
  refine ⟨hdescent, ⨅ k, F D (iter D C β0 k), ?_, ?_⟩
  · exact le_ciInf fun k => hF_nonneg (iter D C β0 k)
  · have hanti : Antitone (fun k => F D (iter D C β0 k)) := antitone_nat_of_succ_le hdescent
    have hbdd : BddBelow (Set.range fun k => F D (iter D C β0 k)) :=
      ⟨0, by rintro _ ⟨k, rfl⟩; exact hF_nonneg _⟩
    exact tendsto_atTop_ciInf hanti hbdd
