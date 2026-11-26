-- Prove2me | solution 1 for Erdos287.denominator_count_lower_bound_from_late_unit_gaps
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T05:28:14.264797+00:00
-- url     : https://prove2.me/submissions/90bb834a-9482-4f7a-a701-a5f06704f427

import Mathlib

open Finset

set_option autoImplicit false

private theorem suffix_gap_slack (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2)
    (T : Finset ℕ) (hT : ∀ j ∈ T, j + 1 < k ∧ f (j + 1) - f j = 1)
    (i : ℕ) (hi : i ≤ k - 1) :
    f (k - 1) + (T.filter (fun j => i ≤ j)).card ≤ f i + 2 * (k - 1 - i) := by
  classical
  refine Nat.decreasingInduction' (n := k - 1) (m := i)
    (P := fun j => f (k - 1) + (T.filter (fun x => j ≤ x)).card ≤ f j + 2 * (k - 1 - j))
    ?_ hi ?_
  · intro j hj _ ih
    have hnext : j + 1 < k := by omega
    have hstep := hgap j hnext
    have hinc := hmono j (j + 1) (by omega) hnext
    have hset :
        T.filter (fun x => j + 1 ≤ x) = (T.filter (fun x => j ≤ x)).erase j := by
      ext x
      simp only [mem_filter, mem_erase]
      constructor
      · rintro ⟨ht, hx⟩
        exact ⟨by omega, ht, by omega⟩
      · rintro ⟨hne, ht, hx⟩
        exact ⟨ht, by omega⟩
    by_cases hmem : j ∈ T.filter (fun x => j ≤ x)
    · have hc := card_erase_add_one hmem
      rw [← hset] at hc
      have hu := (hT j (mem_of_mem_filter _ hmem)).2
      omega
    · rw [erase_eq_of_notMem hmem] at hset
      have hc := congrArg Finset.card hset
      omega
  · have hempty : T.filter (fun j => k - 1 ≤ j) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro j hj
      have ⟨hm, hj⟩ := mem_filter.mp hj
      have hjk := (hT j hm).1
      omega
    change f (k - 1) + (T.filter (fun j => k - 1 ≤ j)).card ≤
      f (k - 1) + 2 * (k - 1 - (k - 1))
    rw [hempty, card_empty, Nat.sub_self, Nat.mul_zero]

/-- Marked unit gaps that follow the first R denominators decrease the
available reciprocal mass for a fixed endpoint and a fixed list length. -/
private theorem late_unit_gap_mass (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2)
    (hA : 2 * (k - 1) < f (k - 1))
    (R : ℕ) (hR : R ≤ k)
    (T : Finset ℕ) (hT : ∀ j ∈ T, j + 1 < k ∧ f (j + 1) - f j = 1)
    (hbefore : ∀ i < R, ∀ j ∈ T, i ≤ j) :
    let M := f (k - 1)
    let A := M - 2 * (k - 1)
    (1 : ℝ) + R * ((T.card : ℝ) / (M : ℝ) ^ 2) ≤
      1 / (A : ℝ) + Real.log ((M : ℝ) / A) / 2 := by
  classical
  dsimp
  let L := k - 1
  let M := f L
  let A := M - 2 * L
  let g (i : ℕ) := A + 2 * i
  let penalty : ℝ := (T.card : ℝ) / (M : ℝ) ^ 2
  change 1 + R * penalty ≤ 1 / (A : ℝ) + Real.log ((M : ℝ) / A) / 2
  have hMk : 2 * L < M := hA
  have hApos : 0 < A := by dsimp [A]; omega
  have hAadd : A + 2 * L = M := by dsimp [A]; omega
  have hLk : L < k := by dsimp [L]; omega
  have hkL : L + 1 = k := by dsimp [L]; omega
  have hgpos (i : ℕ) : (0 : ℝ) < g i := Nat.cast_pos.mpr (by dsimp [g]; omega)
  have hbase (i : ℕ) (hi : i < k) : g i ≤ f i := by
    have hs := suffix_gap_slack k hk f hmono hgap T hT i (by omega)
    change M + (T.filter (fun j => i ≤ j)).card ≤ f i + 2 * (L - i) at hs
    dsimp [g]
    omega
  have hshift (i : ℕ) (hi : i < R) : g i + T.card ≤ f i := by
    have hs := suffix_gap_slack k hk f hmono hgap T hT i (by omega)
    have hself : T.filter (fun j => i ≤ j) = T :=
      filter_eq_self.mpr (fun j hj => hbefore i hi j hj)
    rw [hself] at hs
    change M + T.card ≤ f i + 2 * (L - i) at hs
    dsimp [g]
    omega
  have hmax (i : ℕ) (hi : i < k) : f i ≤ M := by
    rcases eq_or_lt_of_le (show i ≤ L by omega) with he | hl
    · rw [he]
    · exact (hmono i L hl hLk).le
  have hpoint (i : ℕ) (hi : i ∈ range k) :
      (1 : ℝ) / f i + (if i < R then penalty else 0) ≤ 1 / g i := by
    have hik := mem_range.mp hi
    have hg := hbase i hik
    have hfg : (g i : ℝ) ≤ f i := by exact_mod_cast hg
    have hp : (0 : ℝ) < f i := (hgpos i).trans_le hfg
    by_cases hir : i < R
    · rw [if_pos hir]
      have hfm : (f i : ℝ) ≤ M := by exact_mod_cast hmax i hik
      have hprod : (g i : ℝ) * f i ≤ (M : ℝ) ^ 2 := by
        rw [pow_two]
        exact mul_le_mul (hfg.trans hfm) hfm hp.le ((hgpos i).le.trans (hfg.trans hfm))
      have hs : (T.card : ℝ) ≤ (f i : ℝ) - g i := by
        have hcast : (g i : ℝ) + T.card ≤ f i := by exact_mod_cast hshift i hir
        exact le_sub_iff_add_le.mpr (by simpa [add_comm] using hcast)
      have hpen : penalty ≤ (1 : ℝ) / g i - 1 / f i := calc
        _ ≤ (T.card : ℝ) / ((g i : ℝ) * f i) :=
          div_le_div_of_nonneg_left (Nat.cast_nonneg _) (mul_pos (hgpos i) hp) hprod
        _ ≤ ((f i : ℝ) - g i) / ((g i : ℝ) * f i) :=
          div_le_div_of_nonneg_right hs (mul_pos (hgpos i) hp).le
        _ = _ := by field_simp [(hgpos i).ne', hp.ne']
      simpa [add_comm] using le_sub_iff_add_le.mp hpen
    · rw [if_neg hir, add_zero]
      exact one_div_le_one_div_of_le (hgpos i) hfg
  have hsumR : ∑ i ∈ range k, (1 : ℝ) / f i = 1 := by
    simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_natCast, Rat.cast_one] using
      congrArg (fun q : ℚ => (q : ℝ)) hsum
  have hcount : (∑ i ∈ range k, if i < R then penalty else 0) = R * penalty := by
    have hrange : (range k).filter (fun i => i < R) = range R := by
      ext i
      simp only [mem_filter, mem_range]
      omega
    rw [← sum_filter, hrange]
    simp
  have hedges (i : ℕ) (_hi : i ∈ range L) :
      2 * ((1 : ℝ) / g (i + 1)) ≤ Real.log ((g (i + 1) : ℝ) / g i) := by
    rw [mul_one_div]
    have hd : (g (i + 1) : ℝ) = g i + 2 := by
      exact_mod_cast (show g (i + 1) = g i + 2 by dsimp [g]; omega)
    have hf : (g (i + 1) : ℝ) - g i = 2 := by linarith only [hd]
    have hl := Real.one_sub_inv_le_log_of_pos (div_pos (hgpos (i + 1)) (hgpos i))
    rw [inv_div] at hl
    calc
      _ = 1 - (g i : ℝ) / g (i + 1) := by
        rw [← hf, sub_div, div_self (hgpos (i + 1)).ne']
      _ ≤ _ := hl
  have htel : (∑ i ∈ range L, Real.log ((g (i + 1) : ℝ) / g i)) =
      Real.log ((M : ℝ) / A) := by
    calc
      _ = ∑ i ∈ range L, (Real.log (g (i + 1) : ℝ) - Real.log (g i : ℝ)) :=
        sum_congr rfl fun i _ => Real.log_div (hgpos (i + 1)).ne' (hgpos i).ne'
      _ = Real.log (g L : ℝ) - Real.log (g 0 : ℝ) :=
        sum_range_sub (fun i => Real.log (g i : ℝ)) L
      _ = _ := by
        have hMpos : 0 < M := by omega
        rw [show g L = M from hAadd, show g 0 = A by simp [g],
          Real.log_div (Nat.cast_ne_zero.mpr hMpos.ne') (Nat.cast_ne_zero.mpr hApos.ne')]
  have htail : (∑ i ∈ range L, (1 : ℝ) / g (i + 1)) ≤ Real.log ((M : ℝ) / A) / 2 := by
    have hl := sum_le_sum hedges
    rw [← mul_sum, htel] at hl
    exact (le_div_iff₀ (by norm_num)).mpr (by simpa [mul_comm] using hl)
  have hfull := sum_le_sum hpoint
  rw [sum_add_distrib, hsumR, hcount] at hfull
  have hsplit := sum_range_succ' (fun i => (1 : ℝ) / g i) L
  rw [hkL, show g 0 = A by simp [g]] at hsplit
  calc
    _ ≤ ∑ i ∈ range k, (1 : ℝ) / g i := hfull
    _ = 1 / (A : ℝ) + ∑ i ∈ range L, (1 : ℝ) / g (i + 1) := by
      simpa [add_comm] using hsplit
    _ ≤ _ := add_le_add le_rfl htail

/-- Unit gaps that follow the first R denominators increase the minimum
number of denominators at a fixed maximum. -/
theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2)
    (R : ℕ) (hR : R ≤ k)
    (T : Finset ℕ) (hT : ∀ j ∈ T, j + 1 < k ∧ f (j + 1) - f j = 1)
    (hbefore : ∀ i < R, ∀ j ∈ T, i ≤ j) :
    let M := f (k - 1)
    (M : ℝ) - M * Real.exp (-2 - 2 * (R * ((T.card : ℝ) / (M : ℝ) ^ 2))) ≤ 2 * k := by
  let M := f (k - 1)
  let δ : ℝ := R * ((T.card : ℝ) / (M : ℝ) ^ 2)
  change (M : ℝ) - M * Real.exp (-2 - 2 * δ) ≤ 2 * k
  by_cases h : 2 * k < M
  · let A := M - 2 * (k - 1)
    let B := M - 2 * k
    have hA : 2 * (k - 1) < M := by omega
    have hAn : A = B + 2 := by dsimp [A, B]; omega
    have hAr : (A : ℝ) = B + 2 := by exact_mod_cast hAn
    have hBp : (0 : ℝ) < B := Nat.cast_pos.mpr (by dsimp [B]; omega)
    have hAp : (0 : ℝ) < A := by linarith only [hAr, hBp]
    have hMp : (0 : ℝ) < M := Nat.cast_pos.mpr (by omega)
    have hm := late_unit_gap_mass k hk f hmono hsum hgap hA R hR T hT hbefore
    change 1 + δ ≤ 1 / (A : ℝ) + Real.log ((M : ℝ) / A) / 2 at hm
    have hrule := Real.one_sub_inv_le_log_of_pos (div_pos hAp hBp)
    rw [inv_div] at hrule
    have hgapLog : 2 * ((1 : ℝ) / A) ≤ Real.log ((A : ℝ) / B) := by
      calc
        _ = (2 : ℝ) / A := mul_one_div _ _
        _ = 1 - (B : ℝ) / A := by
          rw [← show (A : ℝ) - B = 2 by linarith only [hAr],
            sub_div, div_self hAp.ne']
        _ ≤ _ := hrule
    have hdivide : ((A : ℝ) / B) * ((M : ℝ) / A) = (M : ℝ) / B := by
      field_simp [hAp.ne', hBp.ne']
    have hlogs : Real.log ((M : ℝ) / B) =
        Real.log ((A : ℝ) / B) + Real.log ((M : ℝ) / A) := by
      rw [← Real.log_mul (div_pos hAp hBp).ne' (div_pos hMp hAp).ne', hdivide]
    have hlower : 2 + 2 * δ ≤ Real.log ((M : ℝ) / B) := by
      rw [hlogs]
      linarith only [hm, hgapLog]
    have hexp := Real.exp_le_exp.mpr hlower
    rw [Real.exp_log (div_pos hMp hBp)] at hexp
    have hmul := (le_div_iff₀ hBp).mp hexp
    have hbound : (B : ℝ) ≤ M * Real.exp (-2 - 2 * δ) := by
      rw [show -2 - 2 * δ = -(2 + 2 * δ) by ring, Real.exp_neg, ← div_eq_mul_inv]
      exact (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa [mul_comm] using hmul)
    have hBsum : (B : ℝ) + 2 * k = M := by
      exact_mod_cast (show B + 2 * k = M by dsimp [B]; omega)
    linarith only [hbound, hBsum]
  · have hlarge : (M : ℝ) ≤ 2 * k := by exact_mod_cast Nat.le_of_not_gt h
    have hnonneg : 0 ≤ (M : ℝ) * Real.exp (-2 - 2 * δ) :=
      mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
    linarith only [hlarge, hnonneg]

