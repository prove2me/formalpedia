-- Prove2me | solution 1 for BinPacking.SmallItems.W_le_seventy_one_sixtieths
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T22:38:47.206533+00:00
-- url     : https://prove2.me/submissions/b6018583-0f01-4b9d-818f-65d16b2e3ba4

import Mathlib
import Definitions.Def_BinPacking_SmallItems_Model
import Definitions.Def_BinPacking_SmallItems_Weight

set_option autoImplicit false

namespace P6c9b

open BinPacking.SmallItems

theorem w1_eq_of (k : ℕ) (hk : 0 < k) (x : ℝ) (h1 : 1 / ((k : ℝ) + 1) < x) (h2 : x ≤ 1 / (k : ℝ)) :
    w1 x = 1 / (k : ℝ) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hx : 0 < x := lt_trans (by positivity) h1
  have hfl : ⌊1 / x⌋₊ = k := by
    rw [Nat.floor_eq_iff (by positivity)]
    constructor
    · rw [le_div_iff₀ hx]
      rw [le_div_iff₀ hk'] at h2
      linarith
    · rw [div_lt_iff₀ hx]
      rw [div_lt_iff₀ (by linarith)] at h1
      linarith
  unfold w1
  rw [hfl, one_div]

theorem w1_nonneg (y : ℝ) : 0 ≤ w1 y := by
  unfold w1; positivity

theorem w2_cases (k : ℕ) (hk : 0 < k) (x y : ℝ) (h1 : 1 / ((k : ℝ) + 1) < x)
    (h2 : x ≤ 1 / (k : ℝ)) :
    ((k : ℝ) * x + y ≤ 1 ∧ w2 x y = 1 / (k : ℝ) + ((k : ℝ) - 1) / (k : ℝ) * w1 y) ∨
    (1 < (k : ℝ) * x + y ∧ w2 x y = 1 / (k : ℝ) + w1 y) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hx : 0 < x := lt_trans (by positivity) h1
  have hfl : ⌊1 / x⌋₊ = k := by
    rw [Nat.floor_eq_iff (by positivity)]
    constructor
    · rw [le_div_iff₀ hx]
      rw [le_div_iff₀ hk'] at h2
      linarith
    · rw [div_lt_iff₀ hx]
      rw [div_lt_iff₀ (by linarith)] at h1
      linarith
  have hw := w1_eq_of k hk x h1 h2
  by_cases hr : (k : ℝ) * x + y ≤ 1
  · left
    refine ⟨hr, ?_⟩
    unfold w2
    rw [if_pos ⟨by rw [hfl]; exact ⟨h1, h2⟩, by rw [hfl]; exact hr⟩, hfl, hw]
  · right
    refine ⟨lt_of_not_ge hr, ?_⟩
    unfold w2
    rw [if_neg (by rw [hfl]; exact fun h => hr h.2), hw]

theorem piece_cases (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 2) :
    (1 / 3 < x ∧ x ≤ 1 / 2 ∧ w1 x = 1 / 2) ∨ (1 / 4 < x ∧ x ≤ 1 / 3 ∧ w1 x = 1 / 3) ∨
    (1 / 5 < x ∧ x ≤ 1 / 4 ∧ w1 x = 1 / 4) ∨ (1 / 6 < x ∧ x ≤ 1 / 5 ∧ w1 x = 1 / 5) ∨
    (1 / 7 < x ∧ x ≤ 1 / 6 ∧ w1 x = 1 / 6) := by
  rcases lt_or_ge (1 / 3) x with h3 | h3
  · exact Or.inl ⟨h3, h2, by
      have := w1_eq_of 2 (by norm_num) x (by norm_num; linarith) (by norm_num; linarith)
      simpa using this⟩
  rcases lt_or_ge (1 / 4) x with h4 | h4
  · exact Or.inr <| Or.inl ⟨h4, h3, by
      have := w1_eq_of 3 (by norm_num) x (by norm_num; linarith) (by norm_num; linarith)
      simpa using this⟩
  rcases lt_or_ge (1 / 5) x with h5 | h5
  · exact Or.inr <| Or.inr <| Or.inl ⟨h5, h4, by
      have := w1_eq_of 4 (by norm_num) x (by norm_num; linarith) (by norm_num; linarith)
      simpa using this⟩
  rcases lt_or_ge (1 / 6) x with h6 | h6
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨h6, h5, by
      have := w1_eq_of 5 (by norm_num) x (by norm_num; linarith) (by norm_num; linarith)
      simpa using this⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨h1, h6, by
      have := w1_eq_of 6 (by norm_num) x (by norm_num; linarith) (by norm_num; linarith)
      simpa using this⟩

theorem pc2 (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 2) :
    (1 / 3 < x ∧ x ≤ 1 / 2 ∧ w1 x = 1 / 2) ∨ (1 / 4 < x ∧ x ≤ 1 / 3 ∧ w1 x = 1 / 3) ∨
    (1 / 5 < x ∧ x ≤ 1 / 4 ∧ w1 x = 1 / 4) ∨ (1 / 6 < x ∧ x ≤ 1 / 5 ∧ w1 x = 1 / 5) ∨
    (1 / 7 < x ∧ x ≤ 1 / 6 ∧ w1 x = 1 / 6) := piece_cases x h1 h2

theorem pc3 (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 3) :
    (1 / 4 < x ∧ x ≤ 1 / 3 ∧ w1 x = 1 / 3) ∨
    (1 / 5 < x ∧ x ≤ 1 / 4 ∧ w1 x = 1 / 4) ∨ (1 / 6 < x ∧ x ≤ 1 / 5 ∧ w1 x = 1 / 5) ∨
    (1 / 7 < x ∧ x ≤ 1 / 6 ∧ w1 x = 1 / 6) := by
  rcases piece_cases x h1 (by linarith) with h | h
  · exfalso; linarith [h.1]
  · exact h

theorem pc4 (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 4) :
    (1 / 5 < x ∧ x ≤ 1 / 4 ∧ w1 x = 1 / 4) ∨ (1 / 6 < x ∧ x ≤ 1 / 5 ∧ w1 x = 1 / 5) ∨
    (1 / 7 < x ∧ x ≤ 1 / 6 ∧ w1 x = 1 / 6) := by
  rcases pc3 x h1 (by linarith) with h | h
  · exfalso; linarith [h.1]
  · exact h

theorem pc5 (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 5) :
    (1 / 6 < x ∧ x ≤ 1 / 5 ∧ w1 x = 1 / 5) ∨ (1 / 7 < x ∧ x ≤ 1 / 6 ∧ w1 x = 1 / 6) := by
  rcases pc4 x h1 (by linarith) with h | h
  · exfalso; linarith [h.1]
  · exact h

theorem pc6 (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 6) :
    (1 / 7 < x ∧ x ≤ 1 / 6 ∧ w1 x = 1 / 6) := by
  rcases pc5 x h1 (by linarith) with h | h
  · exfalso; linarith [h.1]
  · exact h

theorem w1le2 (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 2) : w1 x ≤ 1 / 2 := by
  rcases pc2 x h1 h2 with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> rw [h] <;> norm_num

theorem w1le3 (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 3) : w1 x ≤ 1 / 3 := by
  rcases pc3 x h1 h2 with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> rw [h] <;> norm_num

theorem w1le4 (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 4) : w1 x ≤ 1 / 4 := by
  rcases pc4 x h1 h2 with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> rw [h] <;> norm_num

theorem w1le5 (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 5) : w1 x ≤ 1 / 5 := by
  rcases pc5 x h1 h2 with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> rw [h] <;> norm_num

theorem w1le6 (x : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 6) : w1 x ≤ 1 / 6 := by
  rcases pc6 x h1 h2 with ⟨-, -, h⟩ <;> rw [h] <;> norm_num

theorem w2c2 (x y : ℝ) (h1 : 1 / 3 < x) (h2 : x ≤ 1 / 2) :
    (2 * x + y ≤ 1 ∧ w2 x y = 1 / 2 + 1 / 2 * w1 y) ∨ (1 < 2 * x + y ∧ w2 x y = 1 / 2 + w1 y) := by
  have := w2_cases 2 (by norm_num) x y (by norm_num; linarith) (by norm_num; linarith)
  norm_num at this ⊢; exact this

theorem w2c3 (x y : ℝ) (h1 : 1 / 4 < x) (h2 : x ≤ 1 / 3) :
    (3 * x + y ≤ 1 ∧ w2 x y = 1 / 3 + 2 / 3 * w1 y) ∨ (1 < 3 * x + y ∧ w2 x y = 1 / 3 + w1 y) := by
  have := w2_cases 3 (by norm_num) x y (by norm_num; linarith) (by norm_num; linarith)
  norm_num at this ⊢; exact this

theorem w2c4 (x y : ℝ) (h1 : 1 / 5 < x) (h2 : x ≤ 1 / 4) :
    (4 * x + y ≤ 1 ∧ w2 x y = 1 / 4 + 3 / 4 * w1 y) ∨ (1 < 4 * x + y ∧ w2 x y = 1 / 4 + w1 y) := by
  have := w2_cases 4 (by norm_num) x y (by norm_num; linarith) (by norm_num; linarith)
  norm_num at this ⊢; exact this

theorem w2c5 (x y : ℝ) (h1 : 1 / 6 < x) (h2 : x ≤ 1 / 5) :
    (5 * x + y ≤ 1 ∧ w2 x y = 1 / 5 + 4 / 5 * w1 y) ∨ (1 < 5 * x + y ∧ w2 x y = 1 / 5 + w1 y) := by
  have := w2_cases 5 (by norm_num) x y (by norm_num; linarith) (by norm_num; linarith)
  norm_num at this ⊢; exact this

theorem w2c6 (x y : ℝ) (h1 : 1 / 7 < x) (h2 : x ≤ 1 / 6) :
    (6 * x + y ≤ 1 ∧ w2 x y = 1 / 6 + 5 / 6 * w1 y) ∨ (1 < 6 * x + y ∧ w2 x y = 1 / 6 + w1 y) := by
  have := w2_cases 6 (by norm_num) x y (by norm_num; linarith) (by norm_num; linarith)
  norm_num at this ⊢; exact this

/-! ### w12 for the identity, one swap, two disjoint swaps -/

theorem one_mem_pairings (n : ℕ) : (1 : Equiv.Perm (Fin n)) ∈ pairings n := by
  simp [pairings]

theorem swap_mem_pairings {n : ℕ} (i j : Fin n) : Equiv.swap i j ∈ pairings n := by
  simp [pairings, Equiv.swap_mul_self]

theorem swap_comm_of_ne {n : ℕ} (i j k l : Fin n) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k)
    (hjl : j ≠ l) : Equiv.swap i j * Equiv.swap k l = Equiv.swap k l * Equiv.swap i j := by
  apply Equiv.ext; intro x
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  by_cases h1 : x = i
  · subst h1
    rw [Equiv.swap_apply_of_ne_of_ne hik hil, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hjk hjl]
  by_cases h2 : x = j
  · subst h2
    rw [Equiv.swap_apply_of_ne_of_ne hjk hjl, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hik hil]
  by_cases h3 : x = k
  · subst h3
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk),
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hil) (Ne.symm hjl), Equiv.swap_apply_left]
  by_cases h4 : x = l
  · subst h4
    rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (Ne.symm hil) (Ne.symm hjl),
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk), Equiv.swap_apply_right]
  rw [Equiv.swap_apply_of_ne_of_ne h3 h4, Equiv.swap_apply_of_ne_of_ne h1 h2,
    Equiv.swap_apply_of_ne_of_ne h3 h4]

theorem swap2_mem_pairings {n : ℕ} (i j k l : Fin n) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k)
    (hjl : j ≠ l) : Equiv.swap i j * Equiv.swap k l ∈ pairings n := by
  simp only [pairings, Finset.mem_filter, Finset.mem_univ, true_and]
  have hc := swap_comm_of_ne i j k l hik hil hjk hjl
  calc Equiv.swap i j * Equiv.swap k l * (Equiv.swap i j * Equiv.swap k l)
      = Equiv.swap i j * (Equiv.swap k l * Equiv.swap i j) * Equiv.swap k l := by
        simp only [mul_assoc]
    _ = 1 := by
        rw [← hc]
        simp only [Equiv.swap_mul_self_mul, Equiv.swap_mul_self]

theorem sum_w1 (S : List ℝ) : ∑ t : Fin S.length, w1 (S.get t) = (S.map w1).sum := by
  simp

theorem w12_one (S : List ℝ) : w12 S 1 = ∑ i : Fin S.length, w1 (S.get i) := by
  unfold w12
  simp

theorem w12_swap (S : List ℝ) (i j : Fin S.length) (hij : i < j) :
    w12 S (Equiv.swap i j) = (∑ t : Fin S.length, w1 (S.get t)) - w1 (S.get i) - w1 (S.get j)
      + w2 (S.get i) (S.get j) := by
  unfold w12
  have hne : i ≠ j := ne_of_lt hij
  have e1 : (Finset.univ.filter (fun t => Equiv.swap i j t = t)) = (Finset.univ.erase i).erase j := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq]
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2 <;> subst_vars <;> simp_all [eq_comm]
  have e2 : (Finset.univ.filter (fun t => t < Equiv.swap i j t)) = {i} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2 <;> subst_vars <;> simp_all [lt_asymm]
  rw [e1, e2, Finset.sum_singleton, Equiv.swap_apply_left]
  rw [Finset.sum_erase_eq_sub (by simp [Ne.symm hne]), Finset.sum_erase_eq_sub (by simp)]

theorem w12_swap2 (S : List ℝ) (i j k l : Fin S.length) (hij : i < j) (hkl : k < l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    w12 S (Equiv.swap i j * Equiv.swap k l) = (∑ t : Fin S.length, w1 (S.get t))
      - w1 (S.get i) - w1 (S.get j) - w1 (S.get k) - w1 (S.get l)
      + w2 (S.get i) (S.get j) + w2 (S.get k) (S.get l) := by
  unfold w12
  have hne : i ≠ j := ne_of_lt hij
  have hne' : k ≠ l := ne_of_lt hkl
  have vi : (Equiv.swap i j * Equiv.swap k l) i = j := by
    simp [Equiv.swap_apply_of_ne_of_ne hik hil]
  have vj : (Equiv.swap i j * Equiv.swap k l) j = i := by
    simp [Equiv.swap_apply_of_ne_of_ne hjk hjl]
  have vk : (Equiv.swap i j * Equiv.swap k l) k = l := by
    simp [Equiv.swap_apply_of_ne_of_ne (Ne.symm hil) (Ne.symm hjl)]
  have vl : (Equiv.swap i j * Equiv.swap k l) l = k := by
    simp [Equiv.swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk)]
  have vo : ∀ t, t ≠ i → t ≠ j → t ≠ k → t ≠ l → (Equiv.swap i j * Equiv.swap k l) t = t := by
    intro t h1 h2 h3 h4
    simp [Equiv.swap_apply_of_ne_of_ne h3 h4, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have e1 : (Finset.univ.filter (fun t => (Equiv.swap i j * Equiv.swap k l) t = t))
      = (((Finset.univ.erase i).erase j).erase k).erase l := by
    ext t
    rw [Finset.mem_filter]
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, true_and, ne_eq]
    by_cases h1 : t = i
    · rw [h1, vi]; simp [Ne.symm hne]
    by_cases h2 : t = j
    · rw [h2, vj]; simp [hne]
    by_cases h3 : t = k
    · rw [h3, vk]; simp [Ne.symm hne']
    by_cases h4 : t = l
    · rw [h4, vl]; simp [hne']
    rw [vo t h1 h2 h3 h4]; simp [h1, h2, h3, h4]
  have e2 : (Finset.univ.filter (fun t => t < (Equiv.swap i j * Equiv.swap k l) t)) = {i, k} := by
    ext t
    rw [Finset.mem_filter]
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ, true_and]
    by_cases h1 : t = i
    · rw [h1, vi]; simp [hij]
    by_cases h2 : t = j
    · rw [h2, vj]; simp [not_lt.mpr hij.le, hne, Ne.symm hne, hjk]
    by_cases h3 : t = k
    · rw [h3, vk]; simp [hkl]
    by_cases h4 : t = l
    · rw [h4, vl]; simp [not_lt.mpr hkl.le, Ne.symm hil, Ne.symm hne']
    rw [vo t h1 h2 h3 h4]; simp [h1, h3]
  rw [e1, e2, Finset.sum_pair hik, vi, vk]
  rw [Finset.sum_erase_eq_sub (by simp [Ne.symm hil, Ne.symm hjl, Ne.symm hne']),
    Finset.sum_erase_eq_sub (by simp [Ne.symm hik, Ne.symm hjk]),
    Finset.sum_erase_eq_sub (by simp [Ne.symm hne]), Finset.sum_erase_eq_sub (by simp)]
  ring

set_option maxHeartbeats 4000000 in
theorem core1 (x0 : ℝ) (l0 : 1 / 7 < x0) (u0 : x0 ≤ 1 / 2)  (hs : x0 ≤ 1) :
    ∃ σ ∈ pairings [x0].length, w12 [x0] σ ≤ 71 / 60 := by
  exact ⟨1, one_mem_pairings _, by
    rw [w12_one, sum_w1]; show (w1 x0 + 0) ≤ 71 / 60
    have c0 := w1le2 x0 l0 (by linarith only [u0])
    linarith only [c0]⟩

set_option maxHeartbeats 4000000 in
theorem core2 (x0 x1 : ℝ) (l0 : 1 / 7 < x0) (l1 : 1 / 7 < x1) (u0 : x0 ≤ 1 / 2) (o0 : x1 ≤ x0) (hs : x0 + x1 ≤ 1) :
    ∃ σ ∈ pairings [x0, x1].length, w12 [x0, x1] σ ≤ 71 / 60 := by
  exact ⟨1, one_mem_pairings _, by
    rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + 0)) ≤ 71 / 60
    have c0 := w1le2 x0 l0 (by linarith only [u0])
    have c1 := w1le2 x1 l1 (by linarith only [u0, o0])
    linarith only [c0, c1]⟩

set_option maxHeartbeats 4000000 in
theorem core3 (x0 x1 x2 : ℝ) (l0 : 1 / 7 < x0) (l1 : 1 / 7 < x1) (l2 : 1 / 7 < x2) (u0 : x0 ≤ 1 / 2) (o0 : x1 ≤ x0) (o1 : x2 ≤ x1) (hs : x0 + x1 + x2 ≤ 1) :
    ∃ σ ∈ pairings [x0, x1, x2].length, w12 [x0, x1, x2] σ ≤ 71 / 60 := by
  rcases pc2 x0 l0 u0 with ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩
  · rcases pc2 x1 l1 (le_trans o0 b0) with ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩
    · rcases pc2 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · exfalso; linarith only [a2, o0, o1, hs]
      · refine ⟨Equiv.swap ⟨1, (show 1 < 3 by decide)⟩ ⟨2, (show 2 < 3 by decide)⟩, swap_mem_pairings _ _, ?_⟩
        rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 1 < 2 by decide)), sum_w1]
        show (w1 x0 + (w1 x1 + (w1 x2 + 0))) - w1 x1 - w1 x2 + w2 x1 x2 ≤ 71 / 60
        rcases w2c2 x1 x2 a1 b1 with ⟨r1, e1⟩ | ⟨r1, e1⟩
        · norm_num [e1, q0, q1, q2]
        · exfalso; linarith only [o0, hs, r1]
      · refine ⟨Equiv.swap ⟨1, (show 1 < 3 by decide)⟩ ⟨2, (show 2 < 3 by decide)⟩, swap_mem_pairings _ _, ?_⟩
        rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 1 < 2 by decide)), sum_w1]
        show (w1 x0 + (w1 x1 + (w1 x2 + 0))) - w1 x1 - w1 x2 + w2 x1 x2 ≤ 71 / 60
        rcases w2c2 x1 x2 a1 b1 with ⟨r1, e1⟩ | ⟨r1, e1⟩
        · norm_num [e1, q0, q1, q2]
        · exfalso; linarith only [o0, hs, r1]
      · refine ⟨Equiv.swap ⟨1, (show 1 < 3 by decide)⟩ ⟨2, (show 2 < 3 by decide)⟩, swap_mem_pairings _ _, ?_⟩
        rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 1 < 2 by decide)), sum_w1]
        show (w1 x0 + (w1 x1 + (w1 x2 + 0))) - w1 x1 - w1 x2 + w2 x1 x2 ≤ 71 / 60
        rcases w2c2 x1 x2 a1 b1 with ⟨r1, e1⟩ | ⟨r1, e1⟩
        · norm_num [e1, q0, q1, q2]
        · exfalso; linarith only [o0, hs, r1]
      · exact ⟨1, one_mem_pairings _, by rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + 0))) ≤ 71 / 60; norm_num [q0, q1, q2]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + 0))) ≤ 71 / 60
        have c2 := w1le3 x2 l2 (by linarith only [b1, o1])
        linarith only [q0, q1, c2]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + 0))) ≤ 71 / 60
        have c2 := w1le4 x2 l2 (by linarith only [b1, o1])
        linarith only [q0, q1, c2]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + 0))) ≤ 71 / 60
        have c2 := w1le5 x2 l2 (by linarith only [b1, o1])
        linarith only [q0, q1, c2]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + 0))) ≤ 71 / 60
        have c2 := w1le6 x2 l2 (by linarith only [b1, o1])
        linarith only [q0, q1, c2]⟩
  · exact ⟨1, one_mem_pairings _, by
      rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + 0))) ≤ 71 / 60
      have c1 := w1le3 x1 l1 (by linarith only [b0, o0])
      have c2 := w1le3 x2 l2 (by linarith only [b0, o0, o1])
      linarith only [q0, c1, c2]⟩
  · exact ⟨1, one_mem_pairings _, by
      rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + 0))) ≤ 71 / 60
      have c1 := w1le4 x1 l1 (by linarith only [b0, o0])
      have c2 := w1le4 x2 l2 (by linarith only [b0, o0, o1])
      linarith only [q0, c1, c2]⟩
  · exact ⟨1, one_mem_pairings _, by
      rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + 0))) ≤ 71 / 60
      have c1 := w1le5 x1 l1 (by linarith only [b0, o0])
      have c2 := w1le5 x2 l2 (by linarith only [b0, o0, o1])
      linarith only [q0, c1, c2]⟩
  · exact ⟨1, one_mem_pairings _, by
      rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + 0))) ≤ 71 / 60
      have c1 := w1le6 x1 l1 (by linarith only [b0, o0])
      have c2 := w1le6 x2 l2 (by linarith only [b0, o0, o1])
      linarith only [q0, c1, c2]⟩

set_option maxHeartbeats 4000000 in
theorem core4 (x0 x1 x2 x3 : ℝ) (l0 : 1 / 7 < x0) (l1 : 1 / 7 < x1) (l2 : 1 / 7 < x2) (l3 : 1 / 7 < x3) (u0 : x0 ≤ 1 / 2) (o0 : x1 ≤ x0) (o1 : x2 ≤ x1) (o2 : x3 ≤ x2) (hs : x0 + x1 + x2 + x3 ≤ 1) :
    ∃ σ ∈ pairings [x0, x1, x2, x3].length, w12 [x0, x1, x2, x3] σ ≤ 71 / 60 := by
  rcases pc2 x0 l0 u0 with ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩
  · rcases pc2 x1 l1 (le_trans o0 b0) with ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩
    · rcases pc2 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · exfalso; linarith only [a2, l3, o0, o1, hs]
      · exfalso; linarith only [a1, a2, l3, o0, hs]
      · exfalso; linarith only [a1, a2, l3, o0, hs]
      · rcases pc5 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · exfalso; linarith only [a1, a3, o0, o2, hs]
        · refine ⟨Equiv.swap ⟨0, (show 0 < 4 by decide)⟩ ⟨2, (show 2 < 4 by decide)⟩ * Equiv.swap ⟨1, (show 1 < 4 by decide)⟩ ⟨3, (show 3 < 4 by decide)⟩, swap2_mem_pairings _ _ _ _ (Fin.ne_of_val_ne (show 0 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 3 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 3 by decide)), ?_⟩
          rw [w12_swap2 _ _ _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 2 by decide)) (Fin.mk_lt_mk.mpr (show 1 < 3 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 3 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 3 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x0 - w1 x2 - w1 x1 - w1 x3 + w2 x0 x2 + w2 x1 x3 ≤ 71 / 60
          rcases w2c2 x0 x2 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · rcases w2c2 x1 x3 a1 b1 with ⟨r2, e2⟩ | ⟨r2, e2⟩
            · norm_num [e1, e2, q0, q1, q2, q3]
            · exfalso; linarith only [o0, o2, r1, r2]
          · rcases w2c2 x1 x3 a1 b1 with ⟨r2, e2⟩ | ⟨r2, e2⟩
            · exfalso; linarith only [a1, a3, o2, hs, r1]
            · exfalso; linarith only [a3, o2, hs, r1, r2]
      · rcases pc6 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩
        · refine ⟨Equiv.swap ⟨0, (show 0 < 4 by decide)⟩ ⟨2, (show 2 < 4 by decide)⟩ * Equiv.swap ⟨1, (show 1 < 4 by decide)⟩ ⟨3, (show 3 < 4 by decide)⟩, swap2_mem_pairings _ _ _ _ (Fin.ne_of_val_ne (show 0 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 3 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 3 by decide)), ?_⟩
          rw [w12_swap2 _ _ _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 2 by decide)) (Fin.mk_lt_mk.mpr (show 1 < 3 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 3 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 3 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x0 - w1 x2 - w1 x1 - w1 x3 + w2 x0 x2 + w2 x1 x3 ≤ 71 / 60
          rcases w2c2 x0 x2 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · rcases w2c2 x1 x3 a1 b1 with ⟨r2, e2⟩ | ⟨r2, e2⟩
            · norm_num [e1, e2, q0, q1, q2, q3]
            · exfalso; linarith only [o0, o2, r1, r2]
          · rcases w2c2 x1 x3 a1 b1 with ⟨r2, e2⟩ | ⟨r2, e2⟩
            · exfalso; linarith only [a1, a3, o2, hs, r1]
            · exfalso; linarith only [a3, o2, hs, r1, r2]
    · rcases pc3 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · rcases pc3 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · exfalso; linarith only [a3, o0, o1, o2, hs]
        · exfalso; linarith only [a0, a2, a3, o1, hs]
        · exfalso; linarith only [a0, a2, a3, o1, hs]
        · refine ⟨Equiv.swap ⟨0, (show 0 < 4 by decide)⟩ ⟨1, (show 1 < 4 by decide)⟩, swap_mem_pairings _ _, ?_⟩
          rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x0 - w1 x1 + w2 x0 x1 ≤ 71 / 60
          rcases w2c2 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · norm_num [e1, q0, q1, q2, q3]
          · exfalso; linarith only [a2, a3, o1, hs, r1]
      · rcases pc4 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · refine ⟨Equiv.swap ⟨0, (show 0 < 4 by decide)⟩ ⟨1, (show 1 < 4 by decide)⟩, swap_mem_pairings _ _, ?_⟩
          rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x0 - w1 x1 + w2 x0 x1 ≤ 71 / 60
          rcases w2c2 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · norm_num [e1, q0, q1, q2, q3]
          · exfalso; linarith only [a3, o1, o2, hs, r1]
        · refine ⟨Equiv.swap ⟨0, (show 0 < 4 by decide)⟩ ⟨2, (show 2 < 4 by decide)⟩, swap_mem_pairings _ _, ?_⟩
          rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 2 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x0 - w1 x2 + w2 x0 x2 ≤ 71 / 60
          rcases w2c2 x0 x2 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · norm_num [e1, q0, q1, q2, q3]
          · exfalso; linarith only [a1, a3, o2, hs, r1]
        · refine ⟨Equiv.swap ⟨0, (show 0 < 4 by decide)⟩ ⟨3, (show 3 < 4 by decide)⟩, swap_mem_pairings _ _, ?_⟩
          rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 3 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x0 - w1 x3 + w2 x0 x3 ≤ 71 / 60
          rcases w2c2 x0 x3 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · norm_num [e1, q0, q1, q2, q3]
          · exfalso; linarith only [a1, a2, a3, hs, r1]
      · rcases pc5 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · refine ⟨Equiv.swap ⟨0, (show 0 < 4 by decide)⟩ ⟨2, (show 2 < 4 by decide)⟩, swap_mem_pairings _ _, ?_⟩
          rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 2 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x0 - w1 x2 + w2 x0 x2 ≤ 71 / 60
          rcases w2c2 x0 x2 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · norm_num [e1, q0, q1, q2, q3]
          · exfalso; linarith only [a1, a3, o2, hs, r1]
        · refine ⟨Equiv.swap ⟨0, (show 0 < 4 by decide)⟩ ⟨2, (show 2 < 4 by decide)⟩ * Equiv.swap ⟨1, (show 1 < 4 by decide)⟩ ⟨3, (show 3 < 4 by decide)⟩, swap2_mem_pairings _ _ _ _ (Fin.ne_of_val_ne (show 0 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 3 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 3 by decide)), ?_⟩
          rw [w12_swap2 _ _ _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 2 by decide)) (Fin.mk_lt_mk.mpr (show 1 < 3 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 3 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 1 by decide)) (Fin.ne_of_val_ne (show 2 ≠ 3 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x0 - w1 x2 - w1 x1 - w1 x3 + w2 x0 x2 + w2 x1 x3 ≤ 71 / 60
          rcases w2c2 x0 x2 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · rcases w2c3 x1 x3 a1 b1 with ⟨r2, e2⟩ | ⟨r2, e2⟩
            · norm_num [e1, e2, q0, q1, q2, q3]
            · norm_num [e1, e2, q0, q1, q2, q3]
          · rcases w2c3 x1 x3 a1 b1 with ⟨r2, e2⟩ | ⟨r2, e2⟩
            · norm_num [e1, e2, q0, q1, q2, q3]
            · exfalso; linarith only [a3, o2, hs, r1, r2]
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
          have c3 := w1le6 x3 l3 (by linarith only [b2, o2])
          linarith only [q0, q1, q2, c3]⟩
    · rcases pc4 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · rcases pc4 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · refine ⟨Equiv.swap ⟨0, (show 0 < 4 by decide)⟩ ⟨1, (show 1 < 4 by decide)⟩, swap_mem_pairings _ _, ?_⟩
          rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x0 - w1 x1 + w2 x0 x1 ≤ 71 / 60
          rcases w2c2 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · norm_num [e1, q0, q1, q2, q3]
          · exfalso; linarith only [a3, o1, o2, hs, r1]
        · by_cases hsp : 2 * x0 + x3 ≤ 1
          · refine ⟨Equiv.swap ⟨0, (show 0 < 4 by decide)⟩ ⟨3, (show 3 < 4 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 3 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x0 - w1 x3 + w2 x0 x3 ≤ 71 / 60
            rcases w2c2 x0 x3 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3]
            · exfalso; linarith only [r1, hsp]
          · refine ⟨Equiv.swap ⟨2, (show 2 < 4 by decide)⟩ ⟨3, (show 3 < 4 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 2 < 3 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x2 - w1 x3 + w2 x2 x3 ≤ 71 / 60
            rcases w2c4 x2 x3 a2 b2 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3]
            · exfalso; linarith only [o1, hs, r1, hsp]
        · exact ⟨1, one_mem_pairings _, by rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60; norm_num [q0, q1, q2, q3]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
          have c3 := w1le5 x3 l3 (by linarith only [b2, o2])
          linarith only [q0, q1, q2, c3]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
          have c3 := w1le6 x3 l3 (by linarith only [b2, o2])
          linarith only [q0, q1, q2, c3]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
        have c2 := w1le5 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le5 x3 l3 (by linarith only [b1, o1, o2])
        linarith only [q0, q1, c2, c3]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
        have c2 := w1le6 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le6 x3 l3 (by linarith only [b1, o1, o2])
        linarith only [q0, q1, c2, c3]⟩
  · rcases pc3 x1 l1 (le_trans o0 b0) with ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩
    · rcases pc3 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · rcases pc3 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · exfalso; linarith only [a3, o0, o1, o2, hs]
        · refine ⟨Equiv.swap ⟨2, (show 2 < 4 by decide)⟩ ⟨3, (show 3 < 4 by decide)⟩, swap_mem_pairings _ _, ?_⟩
          rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 2 < 3 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x2 - w1 x3 + w2 x2 x3 ≤ 71 / 60
          rcases w2c3 x2 x3 a2 b2 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · norm_num [e1, q0, q1, q2, q3]
          · exfalso; linarith only [o0, o1, hs, r1]
        · refine ⟨Equiv.swap ⟨2, (show 2 < 4 by decide)⟩ ⟨3, (show 3 < 4 by decide)⟩, swap_mem_pairings _ _, ?_⟩
          rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 2 < 3 by decide)), sum_w1]
          show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) - w1 x2 - w1 x3 + w2 x2 x3 ≤ 71 / 60
          rcases w2c3 x2 x3 a2 b2 with ⟨r1, e1⟩ | ⟨r1, e1⟩
          · norm_num [e1, q0, q1, q2, q3]
          · exfalso; linarith only [o0, o1, hs, r1]
        · exact ⟨1, one_mem_pairings _, by rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60; norm_num [q0, q1, q2, q3]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
          have c3 := w1le4 x3 l3 (by linarith only [b2, o2])
          linarith only [q0, q1, q2, c3]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
          have c3 := w1le5 x3 l3 (by linarith only [b2, o2])
          linarith only [q0, q1, q2, c3]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
          have c3 := w1le6 x3 l3 (by linarith only [b2, o2])
          linarith only [q0, q1, q2, c3]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
        have c2 := w1le4 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le4 x3 l3 (by linarith only [b1, o1, o2])
        linarith only [q0, q1, c2, c3]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
        have c2 := w1le5 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le5 x3 l3 (by linarith only [b1, o1, o2])
        linarith only [q0, q1, c2, c3]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
        have c2 := w1le6 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le6 x3 l3 (by linarith only [b1, o1, o2])
        linarith only [q0, q1, c2, c3]⟩
  · exact ⟨1, one_mem_pairings _, by
      rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
      have c1 := w1le4 x1 l1 (by linarith only [b0, o0])
      have c2 := w1le4 x2 l2 (by linarith only [b0, o0, o1])
      have c3 := w1le4 x3 l3 (by linarith only [b0, o0, o1, o2])
      linarith only [q0, c1, c2, c3]⟩
  · exact ⟨1, one_mem_pairings _, by
      rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
      have c1 := w1le5 x1 l1 (by linarith only [b0, o0])
      have c2 := w1le5 x2 l2 (by linarith only [b0, o0, o1])
      have c3 := w1le5 x3 l3 (by linarith only [b0, o0, o1, o2])
      linarith only [q0, c1, c2, c3]⟩
  · exact ⟨1, one_mem_pairings _, by
      rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + 0)))) ≤ 71 / 60
      have c1 := w1le6 x1 l1 (by linarith only [b0, o0])
      have c2 := w1le6 x2 l2 (by linarith only [b0, o0, o1])
      have c3 := w1le6 x3 l3 (by linarith only [b0, o0, o1, o2])
      linarith only [q0, c1, c2, c3]⟩

set_option maxHeartbeats 4000000 in
theorem core5 (x0 x1 x2 x3 x4 : ℝ) (l0 : 1 / 7 < x0) (l1 : 1 / 7 < x1) (l2 : 1 / 7 < x2) (l3 : 1 / 7 < x3) (l4 : 1 / 7 < x4) (u0 : x0 ≤ 1 / 2) (o0 : x1 ≤ x0) (o1 : x2 ≤ x1) (o2 : x3 ≤ x2) (o3 : x4 ≤ x3) (hs : x0 + x1 + x2 + x3 + x4 ≤ 1) :
    ∃ σ ∈ pairings [x0, x1, x2, x3, x4].length, w12 [x0, x1, x2, x3, x4] σ ≤ 71 / 60 := by
  rcases pc2 x0 l0 u0 with ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩
  · rcases pc2 x1 l1 (le_trans o0 b0) with ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩
    · exfalso; linarith only [a1, l4, o0, o2, o3, hs]
    · exfalso; linarith only [a0, a1, l4, o2, o3, hs]
    · rcases pc4 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · exfalso; linarith only [a0, a2, l4, o1, o3, hs]
      · rcases pc5 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · exfalso; linarith only [a0, a1, a3, l4, o2, hs]
        · rcases pc6 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩
          · refine ⟨Equiv.swap ⟨0, (show 0 < 5 by decide)⟩ ⟨1, (show 1 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x0 - w1 x1 + w2 x0 x1 ≤ 71 / 60
            rcases w2c2 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [a4, o1, o2, o3, hs, r1]
      · rcases pc6 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩
        · rcases pc6 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩
          · refine ⟨Equiv.swap ⟨0, (show 0 < 5 by decide)⟩ ⟨1, (show 1 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x0 - w1 x1 + w2 x0 x1 ≤ 71 / 60
            rcases w2c2 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [a4, o1, o2, o3, hs, r1]
    · rcases pc5 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · rcases pc5 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · rcases pc5 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩ | ⟨a4, b4, q4⟩
          · exfalso; linarith only [a0, a4, o1, o2, o3, hs]
          · refine ⟨Equiv.swap ⟨0, (show 0 < 5 by decide)⟩ ⟨1, (show 1 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x0 - w1 x1 + w2 x0 x1 ≤ 71 / 60
            rcases w2c2 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [a4, o1, o2, o3, hs, r1]
        · rcases pc6 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩
          · refine ⟨Equiv.swap ⟨0, (show 0 < 5 by decide)⟩ ⟨1, (show 1 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x0 - w1 x1 + w2 x0 x1 ≤ 71 / 60
            rcases w2c2 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [a4, o1, o2, o3, hs, r1]
      · rcases pc6 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩
        · rcases pc6 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩
          · refine ⟨Equiv.swap ⟨0, (show 0 < 5 by decide)⟩ ⟨1, (show 1 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x0 - w1 x1 + w2 x0 x1 ≤ 71 / 60
            rcases w2c2 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [a4, o1, o2, o3, hs, r1]
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
        have c2 := w1le6 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le6 x3 l3 (by linarith only [b1, o1, o2])
        have c4 := w1le6 x4 l4 (by linarith only [b1, o1, o2, o3])
        linarith only [q0, q1, c2, c3, c4]⟩
  · rcases pc3 x1 l1 (le_trans o0 b0) with ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩
    · rcases pc3 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · exfalso; linarith only [a2, l4, o0, o1, o3, hs]
      · rcases pc4 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · exfalso; linarith only [a1, a3, l4, o0, o2, hs]
        · exfalso; linarith only [a1, a2, a3, l4, o0, hs]
        · rcases pc6 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩
          · refine ⟨Equiv.swap ⟨1, (show 1 < 5 by decide)⟩ ⟨2, (show 2 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 1 < 2 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x1 - w1 x2 + w2 x1 x2 ≤ 71 / 60
            rcases w2c3 x1 x2 a1 b1 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [a4, o0, o2, o3, hs, r1]
      · rcases pc5 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · rcases pc5 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩ | ⟨a4, b4, q4⟩
          · exfalso; linarith only [a1, a4, o0, o2, o3, hs]
          · refine ⟨Equiv.swap ⟨1, (show 1 < 5 by decide)⟩ ⟨2, (show 2 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 1 < 2 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x1 - w1 x2 + w2 x1 x2 ≤ 71 / 60
            rcases w2c3 x1 x2 a1 b1 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [a4, o0, o2, o3, hs, r1]
        · rcases pc6 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩
          · refine ⟨Equiv.swap ⟨1, (show 1 < 5 by decide)⟩ ⟨2, (show 2 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 1 < 2 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x1 - w1 x2 + w2 x1 x2 ≤ 71 / 60
            rcases w2c3 x1 x2 a1 b1 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [a4, o0, o2, o3, hs, r1]
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
          have c3 := w1le6 x3 l3 (by linarith only [b2, o2])
          have c4 := w1le6 x4 l4 (by linarith only [b2, o2, o3])
          linarith only [q0, q1, q2, c3, c4]⟩
    · rcases pc4 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · rcases pc4 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · rcases pc4 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩ | ⟨a4, b4, q4⟩ | ⟨a4, b4, q4⟩
          · exfalso; linarith only [a4, o0, o1, o2, o3, hs]
          · exfalso; linarith only [a0, a3, a4, o1, o2, hs]
          · refine ⟨Equiv.swap ⟨0, (show 0 < 5 by decide)⟩ ⟨1, (show 1 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x0 - w1 x1 + w2 x0 x1 ≤ 71 / 60
            rcases w2c3 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [a3, a4, o1, o2, hs, r1]
        · rcases pc5 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩ | ⟨a4, b4, q4⟩
          · refine ⟨Equiv.swap ⟨2, (show 2 < 5 by decide)⟩ ⟨3, (show 3 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 2 < 3 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x2 - w1 x3 + w2 x2 x3 ≤ 71 / 60
            rcases w2c4 x2 x3 a2 b2 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [a0, a4, o1, o3, hs, r1]
          · refine ⟨Equiv.swap ⟨0, (show 0 < 5 by decide)⟩ ⟨1, (show 1 < 5 by decide)⟩ * Equiv.swap ⟨2, (show 2 < 5 by decide)⟩ ⟨4, (show 4 < 5 by decide)⟩, swap2_mem_pairings _ _ _ _ (Fin.ne_of_val_ne (show 0 ≠ 2 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 4 by decide)) (Fin.ne_of_val_ne (show 1 ≠ 2 by decide)) (Fin.ne_of_val_ne (show 1 ≠ 4 by decide)), ?_⟩
            rw [w12_swap2 _ _ _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)) (Fin.mk_lt_mk.mpr (show 2 < 4 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 2 by decide)) (Fin.ne_of_val_ne (show 0 ≠ 4 by decide)) (Fin.ne_of_val_ne (show 1 ≠ 2 by decide)) (Fin.ne_of_val_ne (show 1 ≠ 4 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x0 - w1 x1 - w1 x2 - w1 x4 + w2 x0 x1 + w2 x2 x4 ≤ 71 / 60
            rcases w2c3 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · rcases w2c4 x2 x4 a2 b2 with ⟨r2, e2⟩ | ⟨r2, e2⟩
              · norm_num [e1, e2, q0, q1, q2, q3, q4]
              · norm_num [e1, e2, q0, q1, q2, q3, q4]
            · rcases w2c4 x2 x4 a2 b2 with ⟨r2, e2⟩ | ⟨r2, e2⟩
              · norm_num [e1, e2, q0, q1, q2, q3, q4]
              · exfalso; linarith only [a3, a4, o1, hs, r1, r2]
        · exact ⟨1, one_mem_pairings _, by
            rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
            have c4 := w1le6 x4 l4 (by linarith only [b3, o3])
            linarith only [q0, q1, q2, q3, c4]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
          have c3 := w1le5 x3 l3 (by linarith only [b2, o2])
          have c4 := w1le5 x4 l4 (by linarith only [b2, o2, o3])
          linarith only [q0, q1, q2, c3, c4]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
          have c3 := w1le6 x3 l3 (by linarith only [b2, o2])
          have c4 := w1le6 x4 l4 (by linarith only [b2, o2, o3])
          linarith only [q0, q1, q2, c3, c4]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
        have c2 := w1le5 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le5 x3 l3 (by linarith only [b1, o1, o2])
        have c4 := w1le5 x4 l4 (by linarith only [b1, o1, o2, o3])
        linarith only [q0, q1, c2, c3, c4]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
        have c2 := w1le6 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le6 x3 l3 (by linarith only [b1, o1, o2])
        have c4 := w1le6 x4 l4 (by linarith only [b1, o1, o2, o3])
        linarith only [q0, q1, c2, c3, c4]⟩
  · rcases pc4 x1 l1 (le_trans o0 b0) with ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩
    · rcases pc4 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · rcases pc4 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · rcases pc4 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩ | ⟨a4, b4, q4⟩ | ⟨a4, b4, q4⟩
          · exfalso; linarith only [a4, o0, o1, o2, o3, hs]
          · refine ⟨Equiv.swap ⟨3, (show 3 < 5 by decide)⟩ ⟨4, (show 4 < 5 by decide)⟩, swap_mem_pairings _ _, ?_⟩
            rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 3 < 4 by decide)), sum_w1]
            show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) - w1 x3 - w1 x4 + w2 x3 x4 ≤ 71 / 60
            rcases w2c4 x3 x4 a3 b3 with ⟨r1, e1⟩ | ⟨r1, e1⟩
            · norm_num [e1, q0, q1, q2, q3, q4]
            · exfalso; linarith only [o0, o1, o2, hs, r1]
          · exact ⟨1, one_mem_pairings _, by rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60; norm_num [q0, q1, q2, q3, q4]⟩
        · exact ⟨1, one_mem_pairings _, by
            rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
            have c4 := w1le5 x4 l4 (by linarith only [b3, o3])
            linarith only [q0, q1, q2, q3, c4]⟩
        · exact ⟨1, one_mem_pairings _, by
            rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
            have c4 := w1le6 x4 l4 (by linarith only [b3, o3])
            linarith only [q0, q1, q2, q3, c4]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
          have c3 := w1le5 x3 l3 (by linarith only [b2, o2])
          have c4 := w1le5 x4 l4 (by linarith only [b2, o2, o3])
          linarith only [q0, q1, q2, c3, c4]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
          have c3 := w1le6 x3 l3 (by linarith only [b2, o2])
          have c4 := w1le6 x4 l4 (by linarith only [b2, o2, o3])
          linarith only [q0, q1, q2, c3, c4]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
        have c2 := w1le5 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le5 x3 l3 (by linarith only [b1, o1, o2])
        have c4 := w1le5 x4 l4 (by linarith only [b1, o1, o2, o3])
        linarith only [q0, q1, c2, c3, c4]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
        have c2 := w1le6 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le6 x3 l3 (by linarith only [b1, o1, o2])
        have c4 := w1le6 x4 l4 (by linarith only [b1, o1, o2, o3])
        linarith only [q0, q1, c2, c3, c4]⟩
  · exact ⟨1, one_mem_pairings _, by
      rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
      have c1 := w1le5 x1 l1 (by linarith only [b0, o0])
      have c2 := w1le5 x2 l2 (by linarith only [b0, o0, o1])
      have c3 := w1le5 x3 l3 (by linarith only [b0, o0, o1, o2])
      have c4 := w1le5 x4 l4 (by linarith only [b0, o0, o1, o2, o3])
      linarith only [q0, c1, c2, c3, c4]⟩
  · exact ⟨1, one_mem_pairings _, by
      rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + 0))))) ≤ 71 / 60
      have c1 := w1le6 x1 l1 (by linarith only [b0, o0])
      have c2 := w1le6 x2 l2 (by linarith only [b0, o0, o1])
      have c3 := w1le6 x3 l3 (by linarith only [b0, o0, o1, o2])
      have c4 := w1le6 x4 l4 (by linarith only [b0, o0, o1, o2, o3])
      linarith only [q0, c1, c2, c3, c4]⟩

set_option maxHeartbeats 4000000 in
theorem core6 (x0 x1 x2 x3 x4 x5 : ℝ) (l0 : 1 / 7 < x0) (l1 : 1 / 7 < x1) (l2 : 1 / 7 < x2) (l3 : 1 / 7 < x3) (l4 : 1 / 7 < x4) (l5 : 1 / 7 < x5) (u0 : x0 ≤ 1 / 2) (o0 : x1 ≤ x0) (o1 : x2 ≤ x1) (o2 : x3 ≤ x2) (o3 : x4 ≤ x3) (o4 : x5 ≤ x4) (hs : x0 + x1 + x2 + x3 + x4 + x5 ≤ 1) :
    ∃ σ ∈ pairings [x0, x1, x2, x3, x4, x5].length, w12 [x0, x1, x2, x3, x4, x5] σ ≤ 71 / 60 := by
  rcases pc2 x0 l0 u0 with ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩ | ⟨a0, b0, q0⟩
  · exfalso; linarith only [a0, l5, o1, o2, o3, o4, hs]
  · rcases pc3 x1 l1 (le_trans o0 b0) with ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩
    · exfalso; linarith only [a1, l5, o0, o2, o3, o4, hs]
    · exfalso; linarith only [a0, a1, l5, o2, o3, o4, hs]
    · rcases pc5 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · exfalso; linarith only [a0, a2, l5, o1, o3, o4, hs]
      · rcases pc6 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩
        · rcases pc6 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩
          · rcases pc6 x5 l5 (le_trans o4 b4) with ⟨a5, b5, q5⟩
            · refine ⟨Equiv.swap ⟨0, (show 0 < 6 by decide)⟩ ⟨1, (show 1 < 6 by decide)⟩, swap_mem_pairings _ _, ?_⟩
              rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 0 < 1 by decide)), sum_w1]
              show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) - w1 x0 - w1 x1 + w2 x0 x1 ≤ 71 / 60
              rcases w2c3 x0 x1 a0 b0 with ⟨r1, e1⟩ | ⟨r1, e1⟩
              · norm_num [e1, q0, q1, q2, q3, q4, q5]
              · exfalso; linarith only [a5, o1, o2, o3, o4, hs, r1]
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
        have c2 := w1le6 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le6 x3 l3 (by linarith only [b1, o1, o2])
        have c4 := w1le6 x4 l4 (by linarith only [b1, o1, o2, o3])
        have c5 := w1le6 x5 l5 (by linarith only [b1, o1, o2, o3, o4])
        linarith only [q0, q1, c2, c3, c4, c5]⟩
  · rcases pc4 x1 l1 (le_trans o0 b0) with ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩
    · rcases pc4 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · exfalso; linarith only [a2, l5, o0, o1, o3, o4, hs]
      · rcases pc5 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · exfalso; linarith only [a1, a3, l5, o0, o2, o4, hs]
        · rcases pc6 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩
          · rcases pc6 x5 l5 (le_trans o4 b4) with ⟨a5, b5, q5⟩
            · refine ⟨Equiv.swap ⟨2, (show 2 < 6 by decide)⟩ ⟨3, (show 3 < 6 by decide)⟩, swap_mem_pairings _ _, ?_⟩
              rw [w12_swap _ _ _ (Fin.mk_lt_mk.mpr (show 2 < 3 by decide)), sum_w1]
              show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) - w1 x2 - w1 x3 + w2 x2 x3 ≤ 71 / 60
              rcases w2c5 x2 x3 a2 b2 with ⟨r1, e1⟩ | ⟨r1, e1⟩
              · norm_num [e1, q0, q1, q2, q3, q4, q5]
              · exfalso; linarith only [a1, a5, o0, o3, o4, hs, r1]
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
          have c3 := w1le6 x3 l3 (by linarith only [b2, o2])
          have c4 := w1le6 x4 l4 (by linarith only [b2, o2, o3])
          have c5 := w1le6 x5 l5 (by linarith only [b2, o2, o3, o4])
          linarith only [q0, q1, q2, c3, c4, c5]⟩
    · rcases pc5 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · rcases pc5 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · rcases pc5 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩ | ⟨a4, b4, q4⟩
          · exfalso; linarith only [a0, a4, l5, o1, o2, o3, hs]
          · exact ⟨1, one_mem_pairings _, by
              rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
              have c5 := w1le6 x5 l5 (by linarith only [b4, o4])
              linarith only [q0, q1, q2, q3, q4, c5]⟩
        · exact ⟨1, one_mem_pairings _, by
            rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
            have c4 := w1le6 x4 l4 (by linarith only [b3, o3])
            have c5 := w1le6 x5 l5 (by linarith only [b3, o3, o4])
            linarith only [q0, q1, q2, q3, c4, c5]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
          have c3 := w1le6 x3 l3 (by linarith only [b2, o2])
          have c4 := w1le6 x4 l4 (by linarith only [b2, o2, o3])
          have c5 := w1le6 x5 l5 (by linarith only [b2, o2, o3, o4])
          linarith only [q0, q1, q2, c3, c4, c5]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
        have c2 := w1le6 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le6 x3 l3 (by linarith only [b1, o1, o2])
        have c4 := w1le6 x4 l4 (by linarith only [b1, o1, o2, o3])
        have c5 := w1le6 x5 l5 (by linarith only [b1, o1, o2, o3, o4])
        linarith only [q0, q1, c2, c3, c4, c5]⟩
  · rcases pc5 x1 l1 (le_trans o0 b0) with ⟨a1, b1, q1⟩ | ⟨a1, b1, q1⟩
    · rcases pc5 x2 l2 (le_trans o1 b1) with ⟨a2, b2, q2⟩ | ⟨a2, b2, q2⟩
      · rcases pc5 x3 l3 (le_trans o2 b2) with ⟨a3, b3, q3⟩ | ⟨a3, b3, q3⟩
        · rcases pc5 x4 l4 (le_trans o3 b3) with ⟨a4, b4, q4⟩ | ⟨a4, b4, q4⟩
          · rcases pc5 x5 l5 (le_trans o4 b4) with ⟨a5, b5, q5⟩ | ⟨a5, b5, q5⟩
            · exfalso; linarith only [a5, o0, o1, o2, o3, o4, hs]
            · exact ⟨1, one_mem_pairings _, by rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60; norm_num [q0, q1, q2, q3, q4, q5]⟩
          · exact ⟨1, one_mem_pairings _, by
              rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
              have c5 := w1le6 x5 l5 (by linarith only [b4, o4])
              linarith only [q0, q1, q2, q3, q4, c5]⟩
        · exact ⟨1, one_mem_pairings _, by
            rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
            have c4 := w1le6 x4 l4 (by linarith only [b3, o3])
            have c5 := w1le6 x5 l5 (by linarith only [b3, o3, o4])
            linarith only [q0, q1, q2, q3, c4, c5]⟩
      · exact ⟨1, one_mem_pairings _, by
          rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
          have c3 := w1le6 x3 l3 (by linarith only [b2, o2])
          have c4 := w1le6 x4 l4 (by linarith only [b2, o2, o3])
          have c5 := w1le6 x5 l5 (by linarith only [b2, o2, o3, o4])
          linarith only [q0, q1, q2, c3, c4, c5]⟩
    · exact ⟨1, one_mem_pairings _, by
        rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
        have c2 := w1le6 x2 l2 (by linarith only [b1, o1])
        have c3 := w1le6 x3 l3 (by linarith only [b1, o1, o2])
        have c4 := w1le6 x4 l4 (by linarith only [b1, o1, o2, o3])
        have c5 := w1le6 x5 l5 (by linarith only [b1, o1, o2, o3, o4])
        linarith only [q0, q1, c2, c3, c4, c5]⟩
  · exact ⟨1, one_mem_pairings _, by
      rw [w12_one, sum_w1]; show (w1 x0 + (w1 x1 + (w1 x2 + (w1 x3 + (w1 x4 + (w1 x5 + 0)))))) ≤ 71 / 60
      have c1 := w1le6 x1 l1 (by linarith only [b0, o0])
      have c2 := w1le6 x2 l2 (by linarith only [b0, o0, o1])
      have c3 := w1le6 x3 l3 (by linarith only [b0, o0, o1, o2])
      have c4 := w1le6 x4 l4 (by linarith only [b0, o0, o1, o2, o3])
      have c5 := w1le6 x5 l5 (by linarith only [b0, o0, o1, o2, o3, o4])
      linarith only [q0, c1, c2, c3, c4, c5]⟩
theorem reduce (S : List ℝ) (hsort : S.Pairwise (fun a b => b ≤ a))
    (hr : ∀ x ∈ S, 1 / 7 < x ∧ x ≤ 1 / 2) (hs : S.sum ≤ 1) :
    ∃ σ ∈ pairings S.length, w12 S σ ≤ 71 / 60 := by
  match S, hsort, hr, hs with
  | [], _, _, _ => exact ⟨1, one_mem_pairings _, by rw [w12_one, sum_w1]; norm_num⟩
  | [x0], hsort, hr, hs =>
    obtain ⟨l0, u0⟩ := hr x0 (by simp)
    simp only [List.sum_cons, List.sum_nil] at hs
    exact core1 x0 l0 u0  (by linarith)
  | [x0, x1], hsort, hr, hs =>
    obtain ⟨l0, u0⟩ := hr x0 (by simp)
    obtain ⟨l1, u1⟩ := hr x1 (by simp)
    have o0 : x1 ≤ x0 := List.rel_of_pairwise_cons hsort (by simp)
    simp only [List.sum_cons, List.sum_nil] at hs
    exact core2 x0 x1 l0 l1 u0 o0 (by linarith)
  | [x0, x1, x2], hsort, hr, hs =>
    obtain ⟨l0, u0⟩ := hr x0 (by simp)
    obtain ⟨l1, u1⟩ := hr x1 (by simp)
    obtain ⟨l2, u2⟩ := hr x2 (by simp)
    have o0 : x1 ≤ x0 := List.rel_of_pairwise_cons hsort (by simp)
    have o1 : x2 ≤ x1 := List.rel_of_pairwise_cons (hsort).of_cons (by simp)
    simp only [List.sum_cons, List.sum_nil] at hs
    exact core3 x0 x1 x2 l0 l1 l2 u0 o0 o1 (by linarith)
  | [x0, x1, x2, x3], hsort, hr, hs =>
    obtain ⟨l0, u0⟩ := hr x0 (by simp)
    obtain ⟨l1, u1⟩ := hr x1 (by simp)
    obtain ⟨l2, u2⟩ := hr x2 (by simp)
    obtain ⟨l3, u3⟩ := hr x3 (by simp)
    have o0 : x1 ≤ x0 := List.rel_of_pairwise_cons hsort (by simp)
    have o1 : x2 ≤ x1 := List.rel_of_pairwise_cons (hsort).of_cons (by simp)
    have o2 : x3 ≤ x2 := List.rel_of_pairwise_cons ((hsort).of_cons).of_cons (by simp)
    simp only [List.sum_cons, List.sum_nil] at hs
    exact core4 x0 x1 x2 x3 l0 l1 l2 l3 u0 o0 o1 o2 (by linarith)
  | [x0, x1, x2, x3, x4], hsort, hr, hs =>
    obtain ⟨l0, u0⟩ := hr x0 (by simp)
    obtain ⟨l1, u1⟩ := hr x1 (by simp)
    obtain ⟨l2, u2⟩ := hr x2 (by simp)
    obtain ⟨l3, u3⟩ := hr x3 (by simp)
    obtain ⟨l4, u4⟩ := hr x4 (by simp)
    have o0 : x1 ≤ x0 := List.rel_of_pairwise_cons hsort (by simp)
    have o1 : x2 ≤ x1 := List.rel_of_pairwise_cons (hsort).of_cons (by simp)
    have o2 : x3 ≤ x2 := List.rel_of_pairwise_cons ((hsort).of_cons).of_cons (by simp)
    have o3 : x4 ≤ x3 := List.rel_of_pairwise_cons (((hsort).of_cons).of_cons).of_cons (by simp)
    simp only [List.sum_cons, List.sum_nil] at hs
    exact core5 x0 x1 x2 x3 x4 l0 l1 l2 l3 l4 u0 o0 o1 o2 o3 (by linarith)
  | [x0, x1, x2, x3, x4, x5], hsort, hr, hs =>
    obtain ⟨l0, u0⟩ := hr x0 (by simp)
    obtain ⟨l1, u1⟩ := hr x1 (by simp)
    obtain ⟨l2, u2⟩ := hr x2 (by simp)
    obtain ⟨l3, u3⟩ := hr x3 (by simp)
    obtain ⟨l4, u4⟩ := hr x4 (by simp)
    obtain ⟨l5, u5⟩ := hr x5 (by simp)
    have o0 : x1 ≤ x0 := List.rel_of_pairwise_cons hsort (by simp)
    have o1 : x2 ≤ x1 := List.rel_of_pairwise_cons (hsort).of_cons (by simp)
    have o2 : x3 ≤ x2 := List.rel_of_pairwise_cons ((hsort).of_cons).of_cons (by simp)
    have o3 : x4 ≤ x3 := List.rel_of_pairwise_cons (((hsort).of_cons).of_cons).of_cons (by simp)
    have o4 : x5 ≤ x4 := List.rel_of_pairwise_cons ((((hsort).of_cons).of_cons).of_cons).of_cons (by simp)
    simp only [List.sum_cons, List.sum_nil] at hs
    exact core6 x0 x1 x2 x3 x4 x5 l0 l1 l2 l3 l4 l5 u0 o0 o1 o2 o3 o4 (by linarith)
  | x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: rest, _, hr, hs =>
    exfalso
    obtain ⟨l0, -⟩ := hr x0 (by simp)
    obtain ⟨l1, -⟩ := hr x1 (by simp)
    obtain ⟨l2, -⟩ := hr x2 (by simp)
    obtain ⟨l3, -⟩ := hr x3 (by simp)
    obtain ⟨l4, -⟩ := hr x4 (by simp)
    obtain ⟨l5, -⟩ := hr x5 (by simp)
    obtain ⟨l6, -⟩ := hr x6 (by simp)
    have hrest : 0 ≤ rest.sum := List.sum_nonneg (fun x hx => le_of_lt (lt_trans (by norm_num) (hr x (by simp [hx])).1))
    simp only [List.sum_cons] at hs
    linarith

end P6c9b

open BinPacking.SmallItems in
theorem solution (X : List ℝ) (hX : ∀ x ∈ X, 1 / 7 < x ∧ x ≤ 1 / 2)
    (hsum : X.sum ≤ 1) :
    W X ≤ 71 / 60 := by
  have hp : (sortDesc X).Perm X := List.mergeSort_perm _ _
  have hsorted : (sortDesc X).Pairwise (fun a b => b ≤ a) := by
    have h := List.pairwise_mergeSort (le := fun a b : ℝ => decide (b ≤ a))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; linarith)
      (fun a b => by simpa using le_total b a) X
    simpa [sortDesc] using h
  obtain ⟨σ, hσ, hw⟩ := P6c9b.reduce (sortDesc X) hsorted (fun x hx => hX x (hp.subset hx))
    (by rw [hp.sum_eq]; exact hsum)
  exact le_trans (Finset.inf'_le _ hσ) hw
