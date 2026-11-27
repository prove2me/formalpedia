-- Prove2me | solution 1 for BarelyTestable.LowerBound.balanced_centers
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:32:46.224873+00:00
-- url     : https://prove2.me/submissions/35224a7b-ce8b-4948-a26a-cc968e8a061b

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Loads
import Theorems.Thm_BarelyTestable_LowerBound_balanced_pairs

set_option autoImplicit false

open BarelyTestable.LowerBound NonmonotoneSubmod.Shared MeasureTheory

namespace BTHelper_balanced_centers

open Finset

section generic

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Maps with one prescribed value: a `1/|β|` fraction of all maps. -/
lemma card_one (x : α) (b : β) :
    (univ.filter (fun f : α → β => f x = b)).card * Fintype.card β = Fintype.card (α → β) := by
  have hf : univ.filter (fun f : α → β => f x = b) =
      Fintype.piFinset (Function.update (fun _ => (univ : Finset β)) x {b}) := by
    ext f
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h j
      by_cases hj : j = x
      · subst hj; simp [h]
      · simp [Function.update_of_ne hj]
    · intro h; simpa using h x
  rw [hf, Fintype.card_piFinset, Fintype.card_pi, prod_eq_mul_prod_sdiff_singleton_of_mem (mem_univ x),
    prod_eq_mul_prod_sdiff_singleton_of_mem (mem_univ x) (fun _ => Fintype.card β)]
  have : ∏ j ∈ univ \ {x}, (Function.update (fun _ => (univ : Finset β)) x {b} j).card =
      ∏ j ∈ univ \ {x}, Fintype.card β := by
    apply prod_congr rfl; intro j hj
    have : j ≠ x := by simpa using hj
    simp [Function.update_of_ne this]
  rw [this]; simp; ring

/-- Maps with two prescribed values at distinct points: a `1/|β|²` fraction of all maps. -/
lemma card_two (x x' : α) (hx : x ≠ x') (b b' : β) :
    (univ.filter (fun f : α → β => f x = b ∧ f x' = b')).card *
      (Fintype.card β * Fintype.card β) = Fintype.card (α → β) := by
  have hf : univ.filter (fun f : α → β => f x = b ∧ f x' = b') =
      Fintype.piFinset (Function.update
        (Function.update (fun _ => (univ : Finset β)) x {b}) x' {b'}) := by
    ext f
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · rintro ⟨h1, h2⟩ j
      by_cases hj' : j = x'
      · subst hj'; simp [h2]
      · rw [Function.update_of_ne hj']
        by_cases hj : j = x
        · subst hj; simp [h1]
        · simp [Function.update_of_ne hj]
    · intro h
      have h1 := h x
      have h2 := h x'
      rw [Function.update_of_ne hx] at h1
      simp only [Function.update_self, mem_singleton] at h1 h2
      exact ⟨h1, h2⟩
  have hxm : x ∈ (univ \ {x'} : Finset α) := by simpa using hx
  rw [hf, Fintype.card_piFinset, Fintype.card_pi, prod_eq_mul_prod_sdiff_singleton_of_mem (mem_univ x'),
    prod_eq_mul_prod_sdiff_singleton_of_mem (mem_univ x') (fun _ => Fintype.card β),
    prod_eq_mul_prod_sdiff_singleton_of_mem hxm, prod_eq_mul_prod_sdiff_singleton_of_mem hxm (fun _ => Fintype.card β)]
  have : ∏ j ∈ ((univ \ {x'}) \ {x}), (Function.update
        (Function.update (fun _ => (univ : Finset β)) x {b}) x' {b'} j).card =
      ∏ j ∈ ((univ \ {x'}) \ {x}), Fintype.card β := by
    apply prod_congr rfl; intro j hj
    simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at hj
    simp [Function.update_of_ne hj.1, Function.update_of_ne hj.2]
  rw [this]; simp [Function.update_of_ne hx]; ring

end generic

variable {m : ℕ}

lemma center_iff (φA φB : LabelMap m) (X Y : HalfSet m) :
    Center φA φB X Y ↔ φA X = parity Y ∧ φB Y = parity X := by
  unfold Center alpha beta
  rw [Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1.symm⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2.symm, h1⟩

/-- Number of label maps (as a real number). -/
noncomputable def Kc (m : ℕ) : ℝ := (Fintype.card (LabelMap m) : ℝ)

lemma count_one (X : HalfSet m) (a : Bits m) :
    ((univ.filter (fun φ : LabelMap m => φ X = a)).card : ℝ) = Kc m / 2 ^ m := by
  have h := card_one X a
  have hb : Fintype.card (Bits m) = 2 ^ m := by simp
  rw [hb] at h
  rw [eq_div_iff (by positivity), Kc]
  exact_mod_cast h

lemma count_two (X X' : HalfSet m) (hX : X ≠ X') (a a' : Bits m) :
    ((univ.filter (fun φ : LabelMap m => φ X = a ∧ φ X' = a')).card : ℝ) =
      Kc m / (2 ^ m * 2 ^ m) := by
  have h := card_two X X' hX a a'
  have hb : Fintype.card (Bits m) = 2 ^ m := by simp
  rw [hb] at h
  rw [eq_div_iff (by positivity), Kc]
  exact_mod_cast h

open Classical in
lemma count_center (X Y : HalfSet m) :
    ((univ.filter (fun r : LabelMap m × LabelMap m => Center r.1 r.2 X Y)).card : ℝ) =
      (Kc m / 2 ^ m) ^ 2 := by
  have : univ.filter (fun r : LabelMap m × LabelMap m => Center r.1 r.2 X Y) =
      (univ.filter (fun φ : LabelMap m => φ X = parity Y)) ×ˢ
        (univ.filter (fun φ : LabelMap m => φ Y = parity X)) := by
    ext r; simp [center_iff]
  rw [this, card_product]; push_cast; rw [count_one, count_one]; ring

open Classical in
lemma count_center2 (X Y X' Y' : HalfSet m) (hX : X ≠ X') (hY : Y ≠ Y') :
    ((univ.filter (fun r : LabelMap m × LabelMap m =>
      Center r.1 r.2 X Y ∧ Center r.1 r.2 X' Y')).card : ℝ) =
      (Kc m / (2 ^ m * 2 ^ m)) ^ 2 := by
  have : univ.filter (fun r : LabelMap m × LabelMap m =>
        Center r.1 r.2 X Y ∧ Center r.1 r.2 X' Y') =
      (univ.filter (fun φ : LabelMap m => φ X = parity Y ∧ φ X' = parity Y')) ×ˢ
        (univ.filter (fun φ : LabelMap m => φ Y = parity X ∧ φ Y' = parity X')) := by
    ext r; simp only [center_iff, mem_filter, mem_univ, true_and, mem_product]; tauto
  rw [this, card_product]; push_cast; rw [count_two X X' hX, count_two Y Y' hY]; ring

open Classical in
/-- Indicator that a pair is a center. -/
noncomputable def ind (r : LabelMap m × LabelMap m) (p : HalfSet m × HalfSet m) : ℝ :=
  if Center r.1 r.2 p.1 p.2 then 1 else 0

lemma ind_nonneg (r : LabelMap m × LabelMap m) (p : HalfSet m × HalfSet m) : 0 ≤ ind r p := by
  unfold ind; split_ifs <;> norm_num

lemma ind_le_one (r : LabelMap m × LabelMap m) (p : HalfSet m × HalfSet m) : ind r p ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

open Classical in
lemma sum_ind (p : HalfSet m × HalfSet m) :
    ∑ r : LabelMap m × LabelMap m, ind r p = (Kc m / 2 ^ m) ^ 2 := by
  rw [← count_center p.1 p.2, Finset.natCast_card_filter]
  rfl

open Classical in
lemma sum_ind2 (p p' : HalfSet m × HalfSet m) (hX : p.1 ≠ p'.1) (hY : p.2 ≠ p'.2) :
    ∑ r : LabelMap m × LabelMap m, ind r p * ind r p' = (Kc m / (2 ^ m * 2 ^ m)) ^ 2 := by
  rw [← count_center2 p.1 p.2 p'.1 p'.2 hX hY, Finset.natCast_card_filter]
  apply sum_congr rfl; intro r _
  unfold ind; split_ifs <;> simp_all

lemma pair_bound (p p' : HalfSet m × HalfSet m) :
    ∑ r : LabelMap m × LabelMap m, ind r p * ind r p' ≤
      (Kc m / (2 ^ m * 2 ^ m)) ^ 2 + (if p.1 = p'.1 then (Kc m / 2 ^ m) ^ 2 else 0) +
        (if p.2 = p'.2 then (Kc m / 2 ^ m) ^ 2 else 0) := by
  have hle : ∑ r : LabelMap m × LabelMap m, ind r p * ind r p' ≤ (Kc m / 2 ^ m) ^ 2 := by
    rw [← sum_ind p]
    apply sum_le_sum; intro r _
    have := ind_nonneg r p; have := ind_le_one r p'
    nlinarith
  have h0 : (0 : ℝ) ≤ (Kc m / (2 ^ m * 2 ^ m)) ^ 2 := by positivity
  have h1 : (0 : ℝ) ≤ (Kc m / 2 ^ m) ^ 2 := by positivity
  by_cases hX : p.1 = p'.1
  · rw [if_pos hX]; split_ifs <;> linarith
  · by_cases hY : p.2 = p'.2
    · rw [if_pos hY, if_neg hX]; linarith
    · rw [if_neg hX, if_neg hY, sum_ind2 p p' hX hY]; linarith

lemma row_sum1 (c : ℝ) (p : HalfSet m × HalfSet m) :
    ∑ p' : HalfSet m × HalfSet m, (if p.1 = p'.1 then c else 0) =
      (Fintype.card (HalfSet m) : ℝ) * c := by
  rw [← Finset.sum_filter, sum_const, nsmul_eq_mul]
  have : univ.filter (fun p' : HalfSet m × HalfSet m => p.1 = p'.1) = {p.1} ×ˢ univ := by
    ext ⟨a, b⟩; simp [eq_comm]
  rw [this, card_product]; simp

lemma row_sum2 (c : ℝ) (p : HalfSet m × HalfSet m) :
    ∑ p' : HalfSet m × HalfSet m, (if p.2 = p'.2 then c else 0) =
      (Fintype.card (HalfSet m) : ℝ) * c := by
  rw [← Finset.sum_filter, sum_const, nsmul_eq_mul]
  have : univ.filter (fun p' : HalfSet m × HalfSet m => p.2 = p'.2) = univ ×ˢ {p.2} := by
    ext ⟨a, b⟩; simp [eq_comm]
  rw [this, card_product]; simp

lemma diag_sum1 (P : Finset (HalfSet m × HalfSet m)) (c : ℝ) (hc : 0 ≤ c) :
    ∑ p ∈ P, ∑ p' ∈ P, (if p.1 = p'.1 then c else 0) ≤
      (Fintype.card (HalfSet m) : ℝ) ^ 3 * c := by
  have hnn : ∀ p p' : HalfSet m × HalfSet m, 0 ≤ (if p.1 = p'.1 then c else 0) := by
    intro p p'; split_ifs <;> linarith
  calc ∑ p ∈ P, ∑ p' ∈ P, (if p.1 = p'.1 then c else 0)
      ≤ ∑ p ∈ P, ∑ p' : HalfSet m × HalfSet m, (if p.1 = p'.1 then c else 0) := by
        apply sum_le_sum; intro p _
        exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun p' _ _ => hnn p p')
    _ ≤ ∑ p : HalfSet m × HalfSet m, ∑ p' : HalfSet m × HalfSet m, (if p.1 = p'.1 then c else 0) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _)
          (fun p _ _ => sum_nonneg (fun p' _ => hnn p p'))
    _ = (Fintype.card (HalfSet m) : ℝ) ^ 3 * c := by
        simp only [row_sum1, sum_const, card_univ, nsmul_eq_mul, Fintype.card_prod]
        push_cast; ring

lemma diag_sum2 (P : Finset (HalfSet m × HalfSet m)) (c : ℝ) (hc : 0 ≤ c) :
    ∑ p ∈ P, ∑ p' ∈ P, (if p.2 = p'.2 then c else 0) ≤
      (Fintype.card (HalfSet m) : ℝ) ^ 3 * c := by
  have hnn : ∀ p p' : HalfSet m × HalfSet m, 0 ≤ (if p.2 = p'.2 then c else 0) := by
    intro p p'; split_ifs <;> linarith
  calc ∑ p ∈ P, ∑ p' ∈ P, (if p.2 = p'.2 then c else 0)
      ≤ ∑ p ∈ P, ∑ p' : HalfSet m × HalfSet m, (if p.2 = p'.2 then c else 0) := by
        apply sum_le_sum; intro p _
        exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun p' _ _ => hnn p p')
    _ ≤ ∑ p : HalfSet m × HalfSet m, ∑ p' : HalfSet m × HalfSet m, (if p.2 = p'.2 then c else 0) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _)
          (fun p _ _ => sum_nonneg (fun p' _ => hnn p p'))
    _ = (Fintype.card (HalfSet m) : ℝ) ^ 3 * c := by
        simp only [row_sum2, sum_const, card_univ, nsmul_eq_mul, Fintype.card_prod]
        push_cast; ring

/-- The center count over a set `P` of pairs. -/
noncomputable def cnt (P : Finset (HalfSet m × HalfSet m)) (r : LabelMap m × LabelMap m) : ℝ :=
  ∑ p ∈ P, ind r p

lemma first_moment (P : Finset (HalfSet m × HalfSet m)) :
    ∑ r : LabelMap m × LabelMap m, cnt P r = P.card * (Kc m / 2 ^ m) ^ 2 := by
  unfold cnt
  rw [Finset.sum_comm]
  simp only [sum_ind, sum_const, nsmul_eq_mul]

lemma second_moment (P : Finset (HalfSet m × HalfSet m)) :
    ∑ r : LabelMap m × LabelMap m, cnt P r ^ 2 ≤
      (P.card : ℝ) ^ 2 * (Kc m / (2 ^ m * 2 ^ m)) ^ 2 +
        2 * (Fintype.card (HalfSet m) : ℝ) ^ 3 * (Kc m / 2 ^ m) ^ 2 := by
  unfold cnt
  have e : ∑ r : LabelMap m × LabelMap m, (∑ p ∈ P, ind r p) ^ 2 =
      ∑ p ∈ P, ∑ p' ∈ P, ∑ r : LabelMap m × LabelMap m, ind r p * ind r p' := by
    simp only [sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    apply sum_congr rfl; intro p _
    rw [Finset.sum_comm]
  rw [e]
  have h1 := diag_sum1 P ((Kc m / 2 ^ m) ^ 2) (by positivity)
  have h2 := diag_sum2 P ((Kc m / 2 ^ m) ^ 2) (by positivity)
  calc ∑ p ∈ P, ∑ p' ∈ P, ∑ r : LabelMap m × LabelMap m, ind r p * ind r p'
      ≤ ∑ p ∈ P, ∑ p' ∈ P, ((Kc m / (2 ^ m * 2 ^ m)) ^ 2 +
          (if p.1 = p'.1 then (Kc m / 2 ^ m) ^ 2 else 0) +
          (if p.2 = p'.2 then (Kc m / 2 ^ m) ^ 2 else 0)) := by
        apply sum_le_sum; intro p _; apply sum_le_sum; intro p' _; exact pair_bound p p'
    _ = (P.card : ℝ) ^ 2 * (Kc m / (2 ^ m * 2 ^ m)) ^ 2 +
          ∑ p ∈ P, ∑ p' ∈ P, (if p.1 = p'.1 then (Kc m / 2 ^ m) ^ 2 else 0) +
          ∑ p ∈ P, ∑ p' ∈ P, (if p.2 = p'.2 then (Kc m / 2 ^ m) ^ 2 else 0) := by
        simp only [sum_add_distrib, sum_const, nsmul_eq_mul]; ring
    _ ≤ _ := by linarith

lemma variance_bound (P : Finset (HalfSet m × HalfSet m)) :
    ∑ r : LabelMap m × LabelMap m, (cnt P r - P.card / (2 ^ m * 2 ^ m)) ^ 2 ≤
      2 * (Fintype.card (HalfSet m) : ℝ) ^ 3 * (Kc m / 2 ^ m) ^ 2 := by
  have h1 := first_moment P
  have h2 := second_moment P
  have hN : (Fintype.card (LabelMap m × LabelMap m) : ℝ) = Kc m * Kc m := by
    rw [Fintype.card_prod, Kc]; push_cast; ring
  have e : ∑ r : LabelMap m × LabelMap m, (cnt P r - P.card / (2 ^ m * 2 ^ m)) ^ 2 =
      ∑ r : LabelMap m × LabelMap m, cnt P r ^ 2 -
        2 * (P.card / (2 ^ m * 2 ^ m)) * ∑ r : LabelMap m × LabelMap m, cnt P r +
        (Fintype.card (LabelMap m × LabelMap m) : ℝ) * (P.card / (2 ^ m * 2 ^ m)) ^ 2 := by
    rw [← Finset.card_univ, ← nsmul_eq_mul, ← Finset.sum_const, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply sum_congr rfl; intro r _; ring
  rw [e, h1, hN]
  have : (2 * (P.card / (2 ^ m * 2 ^ m)) * (P.card * (Kc m / 2 ^ m) ^ 2) : ℝ) -
      Kc m * Kc m * (P.card / (2 ^ m * 2 ^ m)) ^ 2 =
      (P.card : ℝ) ^ 2 * (Kc m / (2 ^ m * 2 ^ m)) ^ 2 := by
    field_simp; ring
  linarith

lemma final_arith (m : ℕ) (hm : 11 ≤ m) : (320 : ℝ) * (2 ^ m * 2 ^ m) ≤ 2 ^ (m * m) := by
  have h1 : 2 * m + 9 ≤ m * m := by nlinarith
  have h2 : (2 : ℝ) ^ (2 * m + 9) ≤ 2 ^ (m * m) := pow_le_pow_right₀ (by norm_num) h1
  have h3 : (2 : ℝ) ^ (2 * m + 9) = 512 * (2 ^ m * 2 ^ m) := by
    rw [pow_add, two_mul, pow_add]; norm_num; ring
  have : (0 : ℝ) ≤ 2 ^ m * 2 ^ m := by positivity
  linarith

end BTHelper_balanced_centers

open BTHelper_balanced_centers in
theorem solution :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      uniformProb (fun r : LabelMap m × LabelMap m =>
        (balancedCenters r.1 r.2 : ℝ) ≤ (1/4 : ℝ) * (1/2 : ℝ)^(2*m) * 2^(2*m^2)) ≤
      (1/10 : ℝ) := by
  classical
  obtain ⟨M0, hM0⟩ := BarelyTestable.LowerBound.balanced_pairs
  refine ⟨M0 + 11, fun m hm => ?_⟩
  have hbp := hM0 m (by omega)
  set P : Finset (HalfSet m × HalfSet m) :=
    Finset.univ.filter (fun p : HalfSet m × HalfSet m =>
      BarelyTestable.LowerBound.Balanced p.1 ∧ BarelyTestable.LowerBound.Balanced p.2) with hP
  have hPc : balancedPairs m = P.card := by
    unfold balancedPairs; rw [hP]
  have hbc : ∀ r : LabelMap m × LabelMap m, (balancedCenters r.1 r.2 : ℝ) = cnt P r := by
    intro r
    unfold balancedCenters cnt ind
    rw [Finset.natCast_card_filter, hP, Finset.sum_filter]
    apply Finset.sum_congr rfl; intro p _
    split_ifs <;> simp_all
  set q : ℝ := 2 ^ m with hq
  set H : ℝ := (Fintype.card (HalfSet m) : ℝ) with hH
  have hHv : H = 2 ^ (m * m) := by
    rw [hH]; simp [Fintype.card_finset]
  have hqpos : 0 < q := by positivity
  have hHpos : 0 < H := by rw [hHv]; positivity
  have hK : 0 < Kc m := by unfold Kc; exact_mod_cast Fintype.card_pos
  set T : ℝ := (1/4 : ℝ) * (1/2 : ℝ)^(2*m) * 2^(2*m^2) with hT
  have hTv : T = H * H / (4 * (q * q)) := by
    rw [hT, hHv, hq, ← pow_add, show m * m + m * m = 2 * m ^ 2 by ring, one_div_pow,
      two_mul m, pow_add]
    field_simp
  have hTpos : 0 < T := by rw [hTv]; positivity
  -- the mean is at least 2T
  have hP2 : H * H / 2 ≤ P.card := by
    rw [← hPc, hHv, ← pow_add, show m * m + m * m = 2 * m ^ 2 by ring]; exact hbp
  set μ : ℝ := P.card / (q * q) with hμ
  have hμT : 2 * T ≤ μ := by
    rw [hTv, hμ]
    rw [show 2 * (H * H / (4 * (q * q))) = (H * H / 2) / (q * q) by field_simp; ring]
    exact div_le_div_of_nonneg_right hP2 (by positivity)
  -- variance
  have hV := variance_bound P
  rw [← hH, ← hq] at hV
  set Bd := Finset.univ.filter (fun r : LabelMap m × LabelMap m => (balancedCenters r.1 r.2 : ℝ) ≤ T)
    with hBd
  have hcnt : (Bd.card : ℝ) * T ^ 2 ≤ 2 * H ^ 3 * (Kc m / q) ^ 2 := by
    calc (Bd.card : ℝ) * T ^ 2 = ∑ r ∈ Bd, T ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ r ∈ Bd, (cnt P r - μ) ^ 2 := by
          apply Finset.sum_le_sum; intro r hr
          rw [hBd, Finset.mem_filter] at hr
          have h1 := hr.2
          rw [hbc r] at h1
          have h0 : 0 ≤ cnt P r := by
            unfold cnt; exact Finset.sum_nonneg (fun p _ => ind_nonneg r p)
          nlinarith
      _ ≤ ∑ r, (cnt P r - μ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun r _ _ => sq_nonneg _)
      _ ≤ 2 * H ^ 3 * (Kc m / q) ^ 2 := hV
  have hBH : (Bd.card : ℝ) * H ≤ 32 * Kc m ^ 2 * (q * q) := by
    rw [hTv] at hcnt
    calc (Bd.card : ℝ) * H = ((Bd.card : ℝ) * (H * H / (4 * (q * q))) ^ 2) *
          (16 * (q * q) ^ 2 / H ^ 3) := by field_simp; ring
      _ ≤ (2 * H ^ 3 * (Kc m / q) ^ 2) * (16 * (q * q) ^ 2 / H ^ 3) :=
          mul_le_mul_of_nonneg_right hcnt (by positivity)
      _ = 32 * Kc m ^ 2 * (q * q) := by field_simp; ring
  have harith : 320 * (q * q) ≤ H := by rw [hq, hHv]; exact final_arith m (by omega)
  have hB10 : 10 * (Bd.card : ℝ) ≤ Kc m ^ 2 := by
    have : 10 * (Bd.card : ℝ) * H ≤ Kc m ^ 2 * H := by nlinarith [sq_nonneg (Kc m)]
    exact le_of_mul_le_mul_right this hHpos
  unfold uniformProb
  have hN : (Fintype.card (LabelMap m × LabelMap m) : ℝ) = Kc m ^ 2 := by
    rw [Fintype.card_prod, Kc]; push_cast; ring
  rw [hN, div_le_iff₀ (by positivity)]
  have : (Finset.univ.filter (fun r : LabelMap m × LabelMap m =>
      (balancedCenters r.1 r.2 : ℝ) ≤ (1/4 : ℝ) * (1/2 : ℝ)^(2*m) * 2^(2*m^2))).card = Bd.card := by
    rw [hBd]
  rw [this]
  linarith
