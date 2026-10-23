-- Prove2me | solution 1 for DQI.Imperfect.theorem_10_1
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-22T20:29:20.645993+00:00
-- url     : https://prove2.me/submissions/fa0f7bd1-e709-49e3-9534-8baa6de1bbc4

import Definitions.Def_DQI_Imperfect_Setting

open Finset Matrix

namespace DQI.Imperfect

lemma sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  have h1 : (1 : ZMod 2) ≠ 0 := by decide
  have ha : a = 0 ∨ a = 1 := by revert a; decide
  have hb : b = 0 ∨ b = 1 := by revert b; decide
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [sgn, h11, h1]

lemma sgn_mul_self (a : ZMod 2) : sgn a * sgn a = 1 := by
  unfold sgn; split_ifs <;> norm_num

lemma sgn_zero' : sgn 0 = 1 := by simp [sgn]

lemma sgn_one' : sgn 1 = -1 := by simp [sgn]

lemma zmod2_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  revert a; decide

lemma sum_sgn_dot {n : ℕ} (z : Fin n → ZMod 2) :
    ∑ x : Fin n → ZMod 2, sgn (z ⬝ᵥ x) = if z = 0 then (2 : ℝ) ^ n else 0 := by
  split_ifs with hz
  · subst hz
    simp [sgn_zero', ZMod.card]
  · obtain ⟨j, hj⟩ : ∃ j, z j ≠ 0 := by
      by_contra h; push_neg at h; exact hz (funext h)
    have hzj := zmod2_ne_zero hj
    have key : ∑ x, sgn (z ⬝ᵥ (x + Pi.single j 1)) = ∑ x, sgn (z ⬝ᵥ x) :=
      Fintype.sum_equiv (Equiv.addRight (Pi.single j 1)) _ _ (fun x => rfl)
    simp_rw [dotProduct_add, dotProduct_single, mul_one, hzj, sgn_add, sgn_one'] at key
    rw [← Finset.sum_mul] at key
    linarith

lemma add_add_eq_zero_iff {n : ℕ} (s s' c : Fin n → ZMod 2) :
    s + s' + c = 0 ↔ s' = s + c := by
  have h : ∀ a b d : ZMod 2, a + b + d = 0 ↔ b = a + d := by decide
  constructor
  · intro hh; funext j; have := congrFun hh j; simp only [Pi.add_apply, Pi.zero_apply] at this
    exact (h _ _ _).1 this
  · intro hh; funext j; have := congrFun hh j; simp only [Pi.add_apply] at this
    simp only [Pi.add_apply, Pi.zero_apply]; exact (h _ _ _).2 this

lemma had_sq_sgn {n : ℕ} (ψ : (Fin n → ZMod 2) → ℝ) (c : Fin n → ZMod 2) :
    ∑ x, hadamard ψ x ^ 2 * sgn (c ⬝ᵥ x) = ∑ s, ψ s * ψ (s + c) := by
  have h2 : (1 / Real.sqrt ((2 : ℝ) ^ n)) ^ 2 = 1 / (2 : ℝ) ^ n := by
    rw [div_pow, Real.sq_sqrt (by positivity)]; simp
  have hpt : ∀ x, hadamard ψ x ^ 2 * sgn (c ⬝ᵥ x) =
      ∑ s, ∑ s', (1 / (2 : ℝ) ^ n) * (ψ s * ψ s') * sgn ((s + s' + c) ⬝ᵥ x) := by
    intro x
    unfold hadamard
    rw [mul_pow, h2, sq, Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun s' _ => ?_)
    rw [add_dotProduct, add_dotProduct, sgn_add, sgn_add]
    ring
  simp_rw [hpt]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_sgn_dot, add_add_eq_zero_iff]
  rw [Finset.sum_eq_single (s + c)]
  · simp; field_simp
  · intro b _ hb; simp [hb]
  · simp

section Comb
variable {m : ℕ}

lemma wt_add_single (y : Fin m → ZMod 2) (i : Fin m) :
    wt (y + Pi.single i 1) = if y i = 0 then wt y + 1 else wt y - 1 := by
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  have h1 : (1 : ZMod 2) ≠ 0 := by decide
  unfold wt
  split_ifs with h
  · have hs : (univ.filter fun j => (y + Pi.single i 1 : Fin m → ZMod 2) j ≠ 0) =
        insert i (univ.filter fun j => y j ≠ 0) := by
      ext j
      by_cases hj : j = i
      · subst hj; simp [h, h1]
      · simp [hj, Pi.single_apply]
    rw [hs, card_insert_of_notMem]; simp [h]
  · have hy := zmod2_ne_zero h
    have hs : (univ.filter fun j => (y + Pi.single i 1 : Fin m → ZMod 2) j ≠ 0) =
        (univ.filter fun j => y j ≠ 0).erase i := by
      ext j
      by_cases hj : j = i
      · subst hj; simp [hy, h11]
      · simp [hj, Pi.single_apply]
    rw [hs, card_erase_of_mem]; simp [h]

lemma wt_le (y : Fin m → ZMod 2) : wt y ≤ m := by
  unfold wt
  calc _ ≤ (univ : Finset (Fin m)).card := card_filter_le _ _
    _ = m := by simp

lemma card_zero_coords (y : Fin m → ZMod 2) :
    (univ.filter fun i => y i = 0).card = m - wt y := by
  have := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Fin m))) (fun i => y i = 0)
  simp only [card_univ, Fintype.card_fin] at this
  have h2 : wt y = (univ.filter fun i => ¬ y i = 0).card := rfl
  omega

noncomputable def G (m j k : ℕ) : ℝ :=
  (if k = j + 1 then ((m : ℝ) - j) else 0) + (if k + 1 = j then (j : ℝ) else 0)

lemma G_nonneg {m j : ℕ} (hj : j ≤ m) (k : ℕ) : 0 ≤ G m j k := by
  unfold G
  have : (j : ℝ) ≤ m := by exact_mod_cast hj
  split_ifs <;> linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]

lemma count_shift (y : Fin m → ZMod 2) (k : ℕ) :
    ∑ i : Fin m, (if wt (y + Pi.single i 1) = k then (1:ℝ) else 0) = G m (wt y) k := by
  simp_rw [wt_add_single]
  have hpt : ∀ i, (if (if y i = 0 then wt y + 1 else wt y - 1) = k then (1:ℝ) else 0) =
      (if y i = 0 then (if wt y + 1 = k then (1:ℝ) else 0)
        else (if wt y - 1 = k then (1:ℝ) else 0)) := by
    intro i; split_ifs <;> simp_all
  simp_rw [hpt]
  rw [Finset.sum_ite]
  simp only [sum_const, nsmul_eq_mul]
  rw [card_zero_coords]
  have h2 : (univ.filter fun i => ¬ y i = 0).card = wt y := rfl
  rw [h2]
  unfold G
  have hw := wt_le y
  push_cast [hw]
  split_ifs <;> simp <;> omega

lemma mem_shell {m k : ℕ} (y : Fin m → ZMod 2) : y ∈ shell m k ↔ wt y = k := by
  simp [shell]

lemma card_shell (m k : ℕ) : (shell m k).card = m.choose k := by
  have : (shell m k).card = (powersetCard k (univ : Finset (Fin m))).card := by
    apply Finset.card_bij (fun y _ => univ.filter fun j => y j ≠ 0)
    · intro y hy
      simp only [shell, mem_filter, mem_univ, true_and] at hy
      simp only [mem_powersetCard, subset_univ, true_and]
      exact hy
    · intro y1 _ y2 _ h
      funext j
      have := congrArg (fun S => j ∈ S) h
      simp only [mem_filter, mem_univ, true_and, eq_iff_iff] at this
      by_cases h1 : y1 j = 0
      · have : y2 j = 0 := by tauto
        rw [h1, this]
      · have h2 : y2 j ≠ 0 := by tauto
        rw [zmod2_ne_zero h1, zmod2_ne_zero h2]
    · intro S hS
      simp only [mem_powersetCard, subset_univ, true_and] at hS
      have h1 : (1 : ZMod 2) ≠ 0 := by decide
      refine ⟨fun j => if j ∈ S then 1 else 0, ?_, ?_⟩
      · rw [mem_shell]
        have : (univ.filter fun j => (if j ∈ S then (1:ZMod 2) else 0) ≠ 0) = S := by
          ext j; simp [h1]
        unfold wt; rw [this]; exact hS
      · ext j; simp [h1]
  rw [this, card_powersetCard, card_univ, Fintype.card_fin]

lemma count_set (T : Finset (Fin m → ZMod 2)) (j k : ℕ) (hT : ∀ y ∈ T, wt y = j) :
    ∑ i : Fin m, ∑ y, (if y ∈ T ∧ wt (y + Pi.single i 1) = k then (1:ℝ) else 0) =
      T.card * G m j k := by
  rw [Finset.sum_comm]
  have hpt : ∀ y, ∑ i : Fin m, (if y ∈ T ∧ wt (y + Pi.single i 1) = k then (1:ℝ) else 0) =
      if y ∈ T then G m j k else 0 := by
    intro y
    by_cases hy : y ∈ T
    · simp only [hy, true_and, if_true]; rw [count_shift, hT y hy]
    · simp [hy]
  simp_rw [hpt]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Finset.filter_univ_mem]  

lemma sum_fin_ite_le {ℓ : ℕ} (j : ℕ) :
    ∑ k : Fin (ℓ+1), (if j = (k:ℕ) then (1:ℝ) else 0) ≤ 1 := by
  by_cases hj : j < ℓ + 1
  · rw [Finset.sum_eq_single ⟨j, hj⟩]
    · simp
    · intro b _ hb; rw [if_neg]; intro h; exact hb (Fin.ext h.symm)
    · simp
  · rw [Finset.sum_eq_zero]
    · norm_num
    intro k _; rw [if_neg]; have := k.isLt; omega

end Comb

section Main
variable {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
  (dec : (Fin n → ZMod 2) → (Fin m → ZMod 2)) {ℓ : ℕ} (w : Fin (ℓ + 1) → ℝ)

noncomputable def uu (m : ℕ) {ℓ : ℕ} (w : Fin (ℓ + 1) → ℝ) (k : Fin (ℓ + 1)) : ℝ :=
  w k / Real.sqrt (m.choose k.val)

noncomputable def alpha (y : Fin m → ZMod 2) : ℝ :=
  ∑ k : Fin (ℓ + 1), if y ∈ Dset B dec k.val then uu m w k else 0

lemma mem_Dset {y : Fin m → ZMod 2} {k : ℕ} :
    y ∈ Dset B dec k ↔ wt y = k ∧ dec (B.transpose.mulVec y) = y := by
  simp [Dset, shell]

lemma mem_Fset {y : Fin m → ZMod 2} {k : ℕ} :
    y ∈ Fset B dec k ↔ wt y = k ∧ dec (B.transpose.mulVec y) ≠ y := by
  simp [Fset, shell]

lemma PtD_eq (v : Fin m → ZMod 2) (s : Fin n → ZMod 2) :
    PtD B v dec ℓ w s = ∑ y, if B.transpose.mulVec y = s then
      alpha B dec w y * sgn (v ⬝ᵥ y) else 0 := by
  unfold PtD alpha uu
  have hpt : ∀ y, (if B.transpose.mulVec y = s then
      (∑ k : Fin (ℓ + 1), if y ∈ Dset B dec k.val then w k / √(m.choose k.val : ℝ) else 0) *
        sgn (v ⬝ᵥ y) else 0) =
      ∑ k : Fin (ℓ + 1), (if y ∈ Dset B dec k.val ∧ B.transpose.mulVec y = s then
        w k / √(m.choose k.val : ℝ) * sgn (v ⬝ᵥ y) else 0) := by
    intro y
    split_ifs with h
    · rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun k _ => ?_)
      split_ifs <;> simp_all
    · symm; apply Finset.sum_eq_zero; intro k _; rw [if_neg]; tauto
  simp_rw [hpt]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hf : (Dset B dec k.val).filter (fun y => B.transpose.mulVec y = s) =
      univ.filter (fun y => y ∈ Dset B dec k.val ∧ B.transpose.mulVec y = s) := by
    ext y; simp
  rw [hf, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  split_ifs <;> simp

lemma pair_sum (f : (Fin m → ZMod 2) → ℝ) (ψ : (Fin n → ZMod 2) → ℝ)
    (hψ : ∀ s, ψ s = ∑ y, if B.transpose.mulVec y = s then f y else 0) (a : Fin n → ZMod 2) :
    ∑ s, ψ s * ψ (s + a) = ∑ y, ∑ y', if B.transpose.mulVec y' = B.transpose.mulVec y + a
      then f y * f y' else 0 := by
  simp_rw [hψ, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y' _ => ?_)
  simp_rw [ite_zero_mul_ite_zero]
  rw [Finset.sum_eq_single (B.transpose.mulVec y)]
  · simp
  · intro b _ hb; rw [if_neg]; tauto
  · simp

lemma num_eq (v : Fin m → ZMod 2) (ψ : (Fin n → ZMod 2) → ℝ) :
    ∑ x, hadamard ψ x ^ 2 * obj B v x = ∑ i, sgn (v i) * ∑ s, ψ s * ψ (s + fun j => B i j) := by
  unfold obj
  have hx : ∀ x, hadamard ψ x ^ 2 * ∑ i, sgn (B.mulVec x i + v i) =
      ∑ i, sgn (v i) * (hadamard ψ x ^ 2 * sgn ((fun j => B i j) ⬝ᵥ x)) := by
    intro x; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have : B.mulVec x i = (fun j => B i j) ⬝ᵥ x := rfl
    rw [this, sgn_add]; ring
  simp_rw [hx]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.mul_sum, had_sq_sgn]

omit B in
lemma den_eq (ψ : (Fin n → ZMod 2) → ℝ) :
    ∑ x, hadamard ψ x ^ 2 = ∑ s, ψ s * ψ (s + 0) := by
  rw [← had_sq_sgn]; simp [sgn_zero']

lemma alpha_of_mem {y : Fin m → ZMod 2} {k : Fin (ℓ + 1)} (hy : y ∈ Dset B dec k.val) :
    alpha B dec w y = uu m w k := by
  unfold alpha
  rw [Finset.sum_eq_single k]
  · simp [hy]
  · intro b _ hb; rw [if_neg]; intro hb'; rw [mem_Dset] at hy hb'
    exact hb (Fin.ext (hb'.1.symm.trans hy.1))
  · simp

lemma alpha_ne_zero {y : Fin m → ZMod 2} (h : alpha B dec w y ≠ 0) :
    dec (B.transpose.mulVec y) = y := by
  unfold alpha at h
  obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  by_cases hy : y ∈ Dset B dec k.val
  · exact ((mem_Dset B dec).1 hy).2
  · simp [hy] at hk

lemma den_alpha (v : Fin m → ZMod 2) :
    ∑ y, ∑ y', (if B.transpose.mulVec y' = B.transpose.mulVec y + 0 then
      alpha B dec w y * sgn (v ⬝ᵥ y) * (alpha B dec w y' * sgn (v ⬝ᵥ y')) else 0) =
      ∑ y, alpha B dec w y ^ 2 := by
  refine Finset.sum_congr rfl (fun y _ => ?_)
  by_cases hα : alpha B dec w y = 0
  · simp [hα]
  · rw [Finset.sum_eq_single y]
    · simp only [add_zero, if_true]
      have := sgn_mul_self (v ⬝ᵥ y)
      calc _ = alpha B dec w y ^ 2 * (sgn (v ⬝ᵥ y) * sgn (v ⬝ᵥ y)) := by ring
        _ = _ := by rw [this, mul_one]
    · intro y' _ hy'
      split_ifs with hc
      · by_cases hα' : alpha B dec w y' = 0
        · simp [hα']
        · exfalso; apply hy'
          rw [← alpha_ne_zero B dec w hα', ← alpha_ne_zero B dec w hα, hc, add_zero]
      · rfl
    · simp

lemma choose_pos_of {m ℓ : ℕ} (hℓ : ℓ ≤ m) (k : Fin (ℓ + 1)) : (0 : ℝ) < m.choose k.val := by
  have := k.isLt
  exact_mod_cast Nat.choose_pos (by omega)

lemma sum_alpha_sq (hℓ : ℓ ≤ m) :
    ∑ y, alpha B dec w y ^ 2 = ∑ k, (w k) ^ 2 * (1 - epsk B dec k.val) := by
  have h1 : ∀ y, alpha B dec w y ^ 2 =
      ∑ k : Fin (ℓ + 1), if y ∈ Dset B dec k.val then uu m w k ^ 2 else 0 := by
    intro y
    have e : alpha B dec w y =
        ∑ k : Fin (ℓ + 1), if y ∈ Dset B dec k.val then uu m w k else 0 := rfl
    rw [sq]
    nth_rewrite 2 [e]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    split_ifs with hy
    · rw [alpha_of_mem B dec w hy, sq]
    · simp
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Finset.filter_univ_mem]
  have hC := choose_pos_of hℓ k
  have hcard : ((Dset B dec k.val).card : ℝ) + (Fset B dec k.val).card = m.choose k.val := by
    have := Finset.card_filter_add_card_filter_not (s := shell m k.val)
      (fun y => dec (B.transpose.mulVec y) = y)
    rw [← card_shell]; exact_mod_cast this
  have hD : ((Dset B dec k.val).card : ℝ) = m.choose k.val - (Fset B dec k.val).card := by
    linarith
  unfold uu epsk
  rw [hD, div_pow, Real.sq_sqrt hC.le]
  field_simp
  try ring

lemma mulVec_single (i : Fin m) :
    B.transpose.mulVec (Pi.single i 1) = fun j => B i j := by
  funext j; simp [Matrix.mulVec, dotProduct_single]

lemma sgn_three (v y y' : Fin m → ZMod 2) (i : Fin m) :
    sgn (v i) * sgn (v ⬝ᵥ y) * sgn (v ⬝ᵥ y') = sgn ((y + y' + Pi.single i 1) ⬝ᵥ v) := by
  rw [add_dotProduct, add_dotProduct, sgn_add, sgn_add, single_dotProduct, one_mul,
    dotProduct_comm y v, dotProduct_comm y' v]; ring

lemma avg_num :
    ∑ v : Fin m → ZMod 2, ∑ i : Fin m, sgn (v i) * ∑ y, ∑ y',
      (if B.transpose.mulVec y' = B.transpose.mulVec y + (fun j => B i j) then
        alpha B dec w y * sgn (v ⬝ᵥ y) * (alpha B dec w y' * sgn (v ⬝ᵥ y')) else 0)
    = 2 ^ m * ∑ i : Fin m, ∑ y, alpha B dec w y * alpha B dec w (y + Pi.single i 1) := by
  have hpt : ∀ (v : Fin m → ZMod 2) (i : Fin m) (y y' : Fin m → ZMod 2),
      sgn (v i) * (if B.transpose.mulVec y' = B.transpose.mulVec y + (fun j => B i j) then
        alpha B dec w y * sgn (v ⬝ᵥ y) * (alpha B dec w y' * sgn (v ⬝ᵥ y')) else 0) =
      (if B.transpose.mulVec y' = B.transpose.mulVec y + (fun j => B i j) then
        alpha B dec w y * alpha B dec w y' * sgn ((y + y' + Pi.single i 1) ⬝ᵥ v) else 0) := by
    intro v i y y'
    split_ifs
    · rw [← sgn_three]; ring
    · simp
  simp_rw [Finset.mul_sum, hpt]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Finset.sum_comm]
  have hy' : ∀ y', ∑ v : Fin m → ZMod 2,
      (if B.transpose.mulVec y' = B.transpose.mulVec y + (fun j => B i j) then
        alpha B dec w y * alpha B dec w y' * sgn ((y + y' + Pi.single i 1) ⬝ᵥ v) else 0) =
      if y' = y + Pi.single i 1 then 2 ^ m * (alpha B dec w y * alpha B dec w y') else 0 := by
    intro y'
    by_cases h : y' = y + Pi.single i 1
    · have hc : B.transpose.mulVec y' = B.transpose.mulVec y + (fun j => B i j) := by
        rw [h, Matrix.mulVec_add, mulVec_single]
      rw [if_pos h]
      simp only [hc, if_true]
      rw [← Finset.mul_sum, sum_sgn_dot, if_pos ((add_add_eq_zero_iff _ _ _).2 h)]; ring
    · rw [if_neg h]
      split_ifs
      · rw [← Finset.mul_sum, sum_sgn_dot,
          if_neg (fun h0 => h ((add_add_eq_zero_iff _ _ _).1 h0)), mul_zero]
      · simp
  simp_rw [hy']
  simp

lemma sum_swap4 {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : A → B → C → D → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc _ = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d := Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _ = ∑ a, ∑ c, ∑ d, ∑ b, f a b c d :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun c _ => Finset.sum_comm))
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := Finset.sum_congr rfl (fun c _ => Finset.sum_comm)

noncomputable def Ecnt (k k' : ℕ) : ℝ :=
  ∑ i : Fin m, ∑ y, if y ∈ Dset B dec k ∧ y + Pi.single i 1 ∈ Dset B dec k' then (1:ℝ) else 0

lemma alpha_pair_eq :
    ∑ i : Fin m, ∑ y, alpha B dec w y * alpha B dec w (y + Pi.single i 1) =
      ∑ k : Fin (ℓ + 1), ∑ k' : Fin (ℓ + 1), uu m w k * uu m w k' * Ecnt B dec k.val k'.val := by
  have h1 : ∀ (i : Fin m) y, alpha B dec w y * alpha B dec w (y + Pi.single i 1) =
      ∑ k : Fin (ℓ + 1), ∑ k' : Fin (ℓ + 1), uu m w k * uu m w k' *
        (if y ∈ Dset B dec k.val ∧ y + Pi.single i 1 ∈ Dset B dec k'.val then 1 else 0) := by
    intro i y; unfold alpha; rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun k' _ => ?_))
    split_ifs <;> simp_all
  simp_rw [h1]
  rw [sum_swap4]
  unfold Ecnt
  simp_rw [Finset.mul_sum]

end Main

section Bounds

lemma Atri_entry {m ℓ : ℕ} (hℓ : ℓ ≤ m) (k k' : Fin (ℓ + 1)) :
    DQI.Semicircle.Atri m ℓ 0 k k' * (√(m.choose k.val : ℝ) * √(m.choose k'.val : ℝ)) =
      m.choose k.val * G m k.val k'.val := by
  obtain ⟨a, ha⟩ := k
  obtain ⟨b, hb⟩ := k'
  simp only [DQI.Semicircle.Atri, G]
  have hcast : ∀ j, j ≤ m →
      (m.choose (j + 1) : ℝ) * ((j : ℝ) + 1) = m.choose j * ((m : ℝ) - j) := by
    intro j hj
    have := Nat.choose_succ_right_eq m j
    have h2 : ((m - j : ℕ) : ℝ) = (m : ℝ) - j := by rw [Nat.cast_sub hj]
    rw [← h2]; exact_mod_cast this
  by_cases h1 : a = b
  · subst h1; simp
  · rw [if_neg h1]
    by_cases h2 : b = a + 1
    · subst h2
      rw [if_pos rfl, if_pos rfl, if_neg (by omega), add_zero]
      have hc := hcast a (by omega)
      have hm : (0 : ℝ) ≤ (m : ℝ) - a := by
        have : (a : ℝ) ≤ m := by exact_mod_cast (show a ≤ m by omega)
        linarith
      have key : ((a : ℝ) + 1) * ((m : ℝ) - a) * ((m.choose a : ℝ) * (m.choose (a + 1) : ℝ)) =
          ((m.choose a : ℝ) * ((m : ℝ) - a)) ^ 2 := by
        linear_combination ((m.choose a : ℝ) * ((m : ℝ) - a)) * hc
      rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity), key,
        Real.sqrt_sq (by positivity)]
    · rw [if_neg h2]
      by_cases h3 : a = b + 1
      · subst h3
        rw [if_pos rfl, if_neg (by omega), if_pos rfl, zero_add]
        have hc := hcast b (by omega)
        have hm : (0 : ℝ) ≤ (m : ℝ) - b := by
          have : (b : ℝ) ≤ m := by exact_mod_cast (show b ≤ m by omega)
          linarith
        have key : ((b : ℝ) + 1) * ((m : ℝ) - b) *
            ((m.choose (b + 1) : ℝ) * (m.choose b : ℝ)) =
            ((m.choose (b + 1) : ℝ) * ((b : ℝ) + 1)) ^ 2 := by
          linear_combination (-((m.choose (b + 1) : ℝ) * ((b : ℝ) + 1))) * hc
        rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity), key,
          Real.sqrt_sq (by positivity)]
        push_cast; ring
      · rw [if_neg h3, if_neg (by omega), if_neg (by omega)]
        simp

lemma add_single_twice {m : ℕ} (y : Fin m → ZMod 2) (i : Fin m) :
    y + Pi.single i 1 + Pi.single i 1 = y := by
  have h : ∀ a b : ZMod 2, a + b + b = a := by decide
  funext j; exact h _ _

lemma sum_shift {m : ℕ} (i : Fin m) (f : (Fin m → ZMod 2) → ℝ) :
    ∑ y : Fin m → ZMod 2, f (y + Pi.single i 1) = ∑ y, f y :=
  Fintype.sum_equiv (Equiv.addRight (Pi.single i (1 : ZMod 2) : Fin m → ZMod 2)) _ _
    (fun _ => rfl)

noncomputable def Icnt (m k k' : ℕ) : ℝ :=
  ∑ i : Fin m, ∑ y : Fin m → ZMod 2,
    if wt y = k ∧ wt (y + Pi.single i 1) = k' then (1:ℝ) else 0

lemma Icnt_eq (m k k' : ℕ) : Icnt m k k' = m.choose k * G m k k' := by
  have := count_set (shell m k) k k' (fun y hy => (mem_shell y).1 hy)
  simp only [mem_shell] at this
  rw [card_shell] at this
  exact this

lemma shell_sum (m k : ℕ) : ∑ y : Fin m → ZMod 2, (if wt y = k then (1:ℝ) else 0) = m.choose k := by
  rw [Finset.sum_boole]
  have : (univ.filter fun y : Fin m → ZMod 2 => wt y = k) = shell m k := rfl
  rw [this, card_shell]

lemma row1 (m ℓ k : ℕ) : ∑ k' : Fin (ℓ + 1), Icnt m k k'.val ≤ m * m.choose k := by
  unfold Icnt
  rw [Finset.sum_comm]
  calc _ ≤ ∑ i : Fin m, ∑ y : Fin m → ZMod 2, (if wt y = k then (1:ℝ) else 0) := by
        apply Finset.sum_le_sum; intro i _
        rw [Finset.sum_comm]
        apply Finset.sum_le_sum; intro y _
        by_cases h : wt y = k
        · simp only [h, true_and, if_true]
          exact sum_fin_ite_le _
        · simp [h]
    _ = m * m.choose k := by simp_rw [shell_sum]; simp

lemma row2 (m ℓ k : ℕ) : ∑ k' : Fin (ℓ + 1), Icnt m k'.val k ≤ m * m.choose k := by
  unfold Icnt
  rw [Finset.sum_comm]
  calc _ ≤ ∑ i : Fin m, ∑ y : Fin m → ZMod 2,
        (if wt (y + Pi.single i 1) = k then (1:ℝ) else 0) := by
        apply Finset.sum_le_sum; intro i _
        rw [Finset.sum_comm]
        apply Finset.sum_le_sum; intro y _
        by_cases h : wt (y + Pi.single i 1) = k
        · simp only [h, and_true, if_true]
          exact sum_fin_ite_le _
        · simp [h]
    _ = m * m.choose k := by
        simp_rw [sum_shift _ (fun y => if wt y = k then (1:ℝ) else 0), shell_sum]; simp

end Bounds

section Final
variable {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
  (dec : (Fin n → ZMod 2) → (Fin m → ZMod 2)) {ℓ : ℕ} (w : Fin (ℓ + 1) → ℝ)

omit B dec in
lemma ind_nonneg (A A' D D' : Prop) [Decidable (A ∧ A')] [Decidable (D ∧ D')]
    (hD : D → A) (hD' : D' → A') :
    0 ≤ (if A ∧ A' then (1:ℝ) else 0) - (if D ∧ D' then (1:ℝ) else 0) := by
  split_ifs <;> first | (exfalso; tauto) | norm_num

omit B dec in
lemma ind_le (A A' D D' F F' : Prop) [Decidable (A ∧ A')] [Decidable (D ∧ D')]
    [Decidable (F ∧ A')] [Decidable (A ∧ F')]
    (hD : D → A) (hD' : D' → A') (hF : A → ¬ D → F) (hF' : A' → ¬ D' → F') :
    (if A ∧ A' then (1:ℝ) else 0) - (if D ∧ D' then (1:ℝ) else 0) ≤
      (if F ∧ A' then (1:ℝ) else 0) + (if A ∧ F' then (1:ℝ) else 0) := by
  split_ifs <;> first | (exfalso; tauto) | norm_num

lemma epsMax_nonneg : 0 ≤ epsMax B dec ℓ := by
  have h0 : epsk B dec 0 ≤ epsMax B dec ℓ :=
    Finset.le_sup' (epsk B dec) (Finset.mem_range.2 (Nat.succ_pos ℓ))
  have : 0 ≤ epsk B dec 0 := by unfold epsk; positivity
  linarith

lemma Fcard_le (hℓ : ℓ ≤ m) (k : Fin (ℓ + 1)) :
    ((Fset B dec k.val).card : ℝ) ≤ epsMax B dec ℓ * m.choose k.val := by
  have h0 : epsk B dec k.val ≤ epsMax B dec ℓ :=
    Finset.le_sup' (epsk B dec) (Finset.mem_range.2 k.isLt)
  have hC := choose_pos_of hℓ k
  unfold epsk at h0
  rwa [div_le_iff₀ hC] at h0

lemma D_bounds (hℓ : ℓ ≤ m) (k k' : Fin (ℓ + 1)) :
    0 ≤ Icnt m k k' - Ecnt B dec k k' ∧
    Icnt m k k' - Ecnt B dec k k' ≤
      epsMax B dec ℓ * (m.choose k.val * G m k k' + m.choose k'.val * G m k' k) := by
  have hP := count_set (Fset B dec k.val) k.val k'.val (fun y hy => ((mem_Fset B dec).1 hy).1)
  have hQ := count_set (Fset B dec k'.val) k'.val k.val (fun y hy => ((mem_Fset B dec).1 hy).1)
  have hQ' : ∑ i : Fin m, ∑ y : Fin m → ZMod 2,
      (if wt y = k.val ∧ y + Pi.single i 1 ∈ Fset B dec k'.val then (1:ℝ) else 0) =
      (Fset B dec k'.val).card * G m k' k := by
    rw [← hQ]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← sum_shift i]
    simp_rw [add_single_twice]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    exact if_congr and_comm rfl rfl
  constructor
  · unfold Icnt Ecnt
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_nonneg; intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_nonneg; intro y _
    exact ind_nonneg _ _ _ _ (fun h => ((mem_Dset B dec).1 h).1) (fun h => ((mem_Dset B dec).1 h).1)
  · have hFk := Fcard_le B dec hℓ k
    have hFk' := Fcard_le B dec hℓ k'
    have hG1 := G_nonneg (m := m) (j := k.val) (by have := k.isLt; omega) k'.val
    have hG2 := G_nonneg (m := m) (j := k'.val) (by have := k'.isLt; omega) k.val
    have hle : Icnt m k k' - Ecnt B dec k k' ≤
        (Fset B dec k.val).card * G m k k' + (Fset B dec k'.val).card * G m k' k := by
      rw [← hP, ← hQ']
      unfold Icnt Ecnt
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum; intro i _
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum; intro y _
      apply ind_le
      · exact fun h => ((mem_Dset B dec).1 h).1
      · exact fun h => ((mem_Dset B dec).1 h).1
      · intro hA hD; rw [mem_Fset]; rw [mem_Dset] at hD; exact ⟨hA, fun h => hD ⟨hA, h⟩⟩
      · intro hA hD; rw [mem_Fset]; rw [mem_Dset] at hD; exact ⟨hA, fun h => hD ⟨hA, h⟩⟩
    nlinarith [mul_le_mul_of_nonneg_right hFk hG1, mul_le_mul_of_nonneg_right hFk' hG2]

lemma main_bound (hℓ : ℓ ≤ m) :
    ∑ k : Fin (ℓ + 1), ∑ k' : Fin (ℓ + 1), uu m w k * uu m w k' * (m.choose k.val * G m k k')
      - 2 * epsMax B dec ℓ * m * ∑ k, w k ^ 2
      ≤ ∑ k : Fin (ℓ + 1), ∑ k' : Fin (ℓ + 1), uu m w k * uu m w k' * Ecnt B dec k k' := by
  set ε := epsMax B dec ℓ with hε
  have hε0 : 0 ≤ ε := epsMax_nonneg B dec
  set X : Fin (ℓ + 1) → Fin (ℓ + 1) → ℝ := fun k k' =>
    m.choose k.val * G m k k' + m.choose k'.val * G m k' k with hX
  have hterm : ∀ k k' : Fin (ℓ + 1),
      uu m w k * uu m w k' * (m.choose k.val * G m k k') - uu m w k * uu m w k' * Ecnt B dec k k'
        ≤ ε / 2 * (uu m w k ^ 2 * X k k' + uu m w k' ^ 2 * X k k') := by
    intro k k'
    obtain ⟨h0, h1⟩ := D_bounds B dec hℓ k k'
    rw [Icnt_eq] at h0 h1
    have hab : uu m w k * uu m w k' ≤ (uu m w k ^ 2 + uu m w k' ^ 2) / 2 := by
      nlinarith [sq_nonneg (uu m w k - uu m w k')]
    have hs : 0 ≤ (uu m w k ^ 2 + uu m w k' ^ 2) / 2 := by positivity
    have e1 := mul_le_mul_of_nonneg_right hab h0
    have e2 := mul_le_mul_of_nonneg_left h1 hs
    calc _ = uu m w k * uu m w k' * (m.choose k.val * G m k k' - Ecnt B dec k k') := by ring
      _ ≤ (uu m w k ^ 2 + uu m w k' ^ 2) / 2 * (m.choose k.val * G m k k' - Ecnt B dec k k') := e1
      _ ≤ (uu m w k ^ 2 + uu m w k' ^ 2) / 2 * (ε * X k k') := e2
      _ = _ := by ring
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ (univ : Finset (Fin (ℓ + 1)))) =>
    Finset.sum_le_sum (fun k' (_ : k' ∈ (univ : Finset (Fin (ℓ + 1)))) => hterm k k'))
  have hsym : ∑ k, ∑ k', uu m w k' ^ 2 * X k k' = ∑ k, ∑ k', uu m w k ^ 2 * X k k' := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun k' _ => ?_))
    simp only [hX]; ring
  have hrow : ∀ k : Fin (ℓ + 1), ∑ k', X k k' ≤ 2 * m * m.choose k.val := by
    intro k
    simp only [hX]
    rw [Finset.sum_add_distrib]
    have r1 := row1 m ℓ k.val
    have r2 := row2 m ℓ k.val
    simp_rw [Icnt_eq] at r1 r2
    linarith
  have hw : ∀ k : Fin (ℓ + 1), uu m w k ^ 2 * m.choose k.val = w k ^ 2 := by
    intro k; unfold uu
    rw [div_pow, Real.sq_sqrt (choose_pos_of hℓ k).le]
    field_simp [(choose_pos_of hℓ k).ne']
  have hA : ∑ k, ∑ k', uu m w k ^ 2 * X k k' ≤ 2 * m * ∑ k, w k ^ 2 := by
    calc ∑ k, ∑ k', uu m w k ^ 2 * X k k' = ∑ k, uu m w k ^ 2 * ∑ k', X k k' := by
          simp_rw [Finset.mul_sum]
      _ ≤ ∑ k, uu m w k ^ 2 * (2 * m * m.choose k.val) :=
          Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hrow k) (sq_nonneg _))
      _ = 2 * m * ∑ k, w k ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [← hw k]; ring
  have hsplit : ∑ k, ∑ k', ε / 2 * (uu m w k ^ 2 * X k k' + uu m w k' ^ 2 * X k k') =
      ε / 2 * ∑ k, ∑ k', uu m w k ^ 2 * X k k' + ε / 2 * ∑ k, ∑ k', uu m w k' ^ 2 * X k k' := by
    simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  have hL : ∑ k : Fin (ℓ + 1), ∑ k' : Fin (ℓ + 1),
      (uu m w k * uu m w k' * (m.choose k.val * G m k k') -
        uu m w k * uu m w k' * Ecnt B dec k k') =
      ∑ k : Fin (ℓ + 1), ∑ k' : Fin (ℓ + 1), uu m w k * uu m w k' * (m.choose k.val * G m k k') -
      ∑ k : Fin (ℓ + 1), ∑ k' : Fin (ℓ + 1), uu m w k * uu m w k' * Ecnt B dec k k' := by
    simp only [Finset.sum_sub_distrib]
  rw [hL, hsplit, hsym] at hsum
  have := mul_le_mul_of_nonneg_left hA hε0
  nlinarith

lemma w_Atri_eq (hℓ : ℓ ≤ m) :
    w ⬝ᵥ (DQI.Semicircle.Atri m ℓ 0).mulVec w =
      ∑ k : Fin (ℓ + 1), ∑ k' : Fin (ℓ + 1), uu m w k * uu m w k' * (m.choose k.val * G m k k') := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun k' _ => ?_))
  rw [← Atri_entry hℓ k k']
  unfold uu
  have h1 := Real.sqrt_pos.2 (choose_pos_of hℓ k)
  have h2 := Real.sqrt_pos.2 (choose_pos_of hℓ k')
  field_simp
  try ring

end Final

theorem theorem_10_1 (m n ℓ : ℕ) (hℓ : ℓ ≤ m)
    (B : Matrix (Fin m) (Fin n) (ZMod 2)) (dec : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (w : Fin (ℓ + 1) → ℝ)
    (hN : 0 < (∑ k, (w k) ^ 2 * (1 - epsk B dec k.val))) :
    ((w ⬝ᵥ (DQI.Semicircle.Atri m ℓ 0).mulVec w) -
        2 * epsMax B dec ℓ * ((m : ℝ) + 1) * (w ⬝ᵥ w)) /
      (∑ k, (w k) ^ 2 * (1 - epsk B dec k.val)) ≤
      avgV m (fun v => expObj B v (hadamard (PtD B v dec ℓ w))) := by
  have hexp : ∀ v, expObj B v (hadamard (PtD B v dec ℓ w)) =
      (∑ i : Fin m, sgn (v i) * ∑ y, ∑ y',
        (if B.transpose.mulVec y' = B.transpose.mulVec y + (fun j => B i j) then
          alpha B dec w y * sgn (v ⬝ᵥ y) * (alpha B dec w y' * sgn (v ⬝ᵥ y')) else 0)) /
      (∑ k, (w k) ^ 2 * (1 - epsk B dec k.val)) := by
    intro v
    have hψ := PtD_eq B dec w v
    have hp := pair_sum B (fun y => alpha B dec w y * sgn (v ⬝ᵥ y)) (PtD B v dec ℓ w) hψ
    beta_reduce at hp
    unfold expObj
    rw [num_eq, den_eq]
    simp_rw [hp]
    rw [den_alpha, sum_alpha_sq B dec w hℓ]
  have havg : avgV m (fun v => expObj B v (hadamard (PtD B v dec ℓ w))) =
      (∑ i : Fin m, ∑ y, alpha B dec w y * alpha B dec w (y + Pi.single i 1)) /
      (∑ k, (w k) ^ 2 * (1 - epsk B dec k.val)) := by
    unfold avgV
    simp_rw [hexp]
    rw [← Finset.sum_div, avg_num]
    field_simp
  rw [havg]
  apply div_le_div_of_nonneg_right _ hN.le
  rw [alpha_pair_eq, w_Atri_eq w hℓ]
  have hmb := main_bound B dec w hℓ
  have hww : w ⬝ᵥ w = ∑ k, w k ^ 2 := by simp [dotProduct, sq]
  have hε0 := epsMax_nonneg B dec (ℓ := ℓ)
  have hW : 0 ≤ ∑ k, w k ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  rw [hww]
  nlinarith [mul_nonneg hε0 hW]

end DQI.Imperfect


-- Platform entry point: restates the target verbatim.
namespace DQI.Imperfect

theorem _root_.solution (m n ℓ : ℕ) (hℓ : ℓ ≤ m)
    (B : Matrix (Fin m) (Fin n) (ZMod 2)) (dec : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (w : Fin (ℓ + 1) → ℝ)
    (hN : 0 < (∑ k, (w k) ^ 2 * (1 - epsk B dec k.val))) :
    ((w ⬝ᵥ (DQI.Semicircle.Atri m ℓ 0).mulVec w) -
        2 * epsMax B dec ℓ * ((m : ℝ) + 1) * (w ⬝ᵥ w)) /
      (∑ k, (w k) ^ 2 * (1 - epsk B dec k.val)) ≤
      avgV m (fun v => expObj B v (hadamard (PtD B v dec ℓ w))) := by
  apply @DQI.Imperfect.theorem_10_1 <;> assumption

end DQI.Imperfect
