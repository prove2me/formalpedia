-- Prove2me | solution 1 for DQI.Imperfect.lemma_10_7
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T07:05:30.016799+00:00
-- url     : https://prove2.me/submissions/2f6c3625-9780-4e8f-80a5-f3d5b022a9f5

import Mathlib
import Definitions.Def_DQI_Imperfect_Setting

set_option autoImplicit false
open scoped BigOperators

namespace DecoderResearch

theorem quadratic_bound {I : Type*} [Fintype I] (E : Matrix I I ℝ) (C : ℝ)
    (hnn : ∀ i j, 0 ≤ E i j) (hsym : ∀ i j, E i j = E j i)
    (hrow : ∀ i, ∑ j, E i j ≤ C) (u : I → ℝ) :
    |u ⬝ᵥ E.mulVec u| ≤ C * (u ⬝ᵥ u) := by
  classical
  have hentry (i j : I) : |u i * (E i j * u j)| ≤ E i j * (u i ^ 2 + u j ^ 2) / 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (hnn i j)]
    have hh : 2 * |u i| * |u j| ≤ u i ^ 2 + u j ^ 2 := by
      nlinarith [sq_nonneg (|u i| - |u j|), sq_abs (u i), sq_abs (u j)]
    nlinarith [mul_nonneg (hnn i j) (show 0 ≤ u i ^ 2 + u j ^ 2 - 2 * |u i| * |u j| by linarith)]
  have hcol (j : I) : ∑ i, E i j ≤ C := by
    simpa only [hsym] using hrow j
  have hleft : (∑ i, (∑ j, E i j) * u i ^ 2) ≤ C * ∑ i, u i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _))
  have hright : (∑ j, (∑ i, E i j) * u j ^ 2) ≤ C * ∑ j, u j ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _))
  have hid : (∑ i, ∑ j, E i j * (u i ^ 2 + u j ^ 2) / 2) =
      ((∑ i, (∑ j, E i j) * u i ^ 2) + (∑ j, (∑ i, E i j) * u j ^ 2)) / 2 := by
    simp_rw [mul_add, add_div, Finset.sum_add_distrib]
    congr 1
    · simp_rw [← Finset.sum_div, ← Finset.sum_mul]
    · rw [Finset.sum_comm]
      simp_rw [← Finset.sum_div, ← Finset.sum_mul]
  calc
    |u ⬝ᵥ E.mulVec u| = |∑ i, ∑ j, u i * (E i j * u j)| := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    _ ≤ ∑ i, ∑ j, |u i * (E i j * u j)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, E i j * (u i ^ 2 + u j ^ 2) / 2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
    _ ≤ C * (u ⬝ᵥ u) := by
      rw [hid]
      simp only [dotProduct]
      simp_rw [← sq]
      linarith

end DecoderResearch

namespace DecoderResearch

private theorem edge_card_symm {m : ℕ}
    (X Y F G : Finset (Fin m → ZMod 2)) (i : Fin m) :
    (((X ×ˢ G) ∪ (F ×ˢ Y)).filter
      (fun yy => yy.1 + yy.2 + Pi.single i 1 = 0)).card =
    (((Y ×ˢ F) ∪ (G ×ˢ X)).filter
      (fun yy => yy.1 + yy.2 + Pi.single i 1 = 0)).card := by
  classical
  apply Finset.card_bij (fun yy _ => yy.swap)
  · intro yy hy
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_product] at hy ⊢
    refine ⟨?_, ?_⟩
    · rcases hy.1 with h | h
      · exact Or.inr ⟨h.2, h.1⟩
      · exact Or.inl ⟨h.2, h.1⟩
    · simpa only [Prod.swap, add_comm] using hy.2
  · intro a _ b _ h
    simpa using congrArg Prod.swap h
  · intro yy hy
    refine ⟨yy.swap, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_product] at hy ⊢
    refine ⟨?_, ?_⟩
    · rcases hy.1 with h | h
      · exact Or.inr ⟨h.2, h.1⟩
      · exact Or.inl ⟨h.2, h.1⟩
    · simpa only [Prod.swap, add_comm] using hy.2

open DQI.Imperfect in
theorem Emat_symmetric {m n ℓ : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (dec : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (k j : Fin (ℓ + 1)) :
    Emat B dec ℓ k j = Emat B dec ℓ j k := by
  classical
  simp only [Emat]
  congr 1
  · rw [mul_comm (Nat.choose m k.val : ℝ)]
  · exact congrArg (fun z : ℕ => (z : ℝ)) (Finset.sum_congr rfl fun i _ =>
      edge_card_symm (shell m k.val) (shell m j.val)
        (Fset B dec k.val) (Fset B dec j.val) i)

open DQI.Imperfect in
theorem Emat_nonneg {m n ℓ : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (dec : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (k j : Fin (ℓ + 1)) :
    0 ≤ Emat B dec ℓ k j := by
  unfold Emat
  positivity

end DecoderResearch

namespace DecoderResearch
open DQI.Imperfect

theorem adjacent_weights {m : ℕ} (y z : Fin m → ZMod 2) (i : Fin m)
    (h : y + z + Pi.single i 1 = 0) : wt y + 1 = wt z ∨ wt z + 1 = wt y := by
  classical
  have heq (j : Fin m) (hj : j ≠ i) : y j = z j := by
    have hh : y j + z j = 0 := by simpa [Pi.single_apply, hj] using congrFun h j
    simpa using eq_neg_of_add_eq_zero_left hh
  have hi : y i + z i + 1 = 0 := by simpa using congrFun h i
  have hb : ∀ a b : ZMod 2, a + b + 1 = 0 →
      (a = 0 ∧ b ≠ 0) ∨ (b = 0 ∧ a ≠ 0) := by decide
  have herase : (Finset.univ.filter (fun j => y j ≠ 0)).erase i =
      (Finset.univ.filter (fun j => z j ≠ 0)).erase i := by
    ext j
    by_cases hj : j = i
    · simp [hj]
    · simp [hj, heq j hj]
  rcases hb (y i) (z i) hi with ⟨hy, hz⟩ | ⟨hz, hy⟩
  · left
    have hny : i ∉ Finset.univ.filter (fun j => y j ≠ 0) := by simp [hy]
    have hmz : i ∈ Finset.univ.filter (fun j => z j ≠ 0) := by simp [hz]
    have hh := Finset.card_erase_add_one hmz
    rw [← herase, Finset.erase_eq_of_notMem hny] at hh
    exact hh
  · right
    have hnz : i ∉ Finset.univ.filter (fun j => z j ≠ 0) := by simp [hz]
    have hmy : i ∈ Finset.univ.filter (fun j => y j ≠ 0) := by simp [hy]
    have hh := Finset.card_erase_add_one hmy
    rw [herase, Finset.erase_eq_of_notMem hnz] at hh
    exact hh

theorem Emat_offdiagonal_zero {m n ℓ : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (dec : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (k j : Fin (ℓ + 1))
    (hkj : k.val + 1 ≠ j.val) (hjk : j.val + 1 ≠ k.val) :
    Emat B dec ℓ k j = 0 := by
  classical
  have he (i : Fin m) :
      (((shell m k.val ×ˢ Fset B dec j.val) ∪ (Fset B dec k.val ×ˢ shell m j.val)).filter
        (fun yy => yy.1 + yy.2 + Pi.single i 1 = 0)) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro yy hy
    have hy' := Finset.mem_filter.mp hy
    have hs : yy.1 ∈ shell m k.val ∧ yy.2 ∈ shell m j.val := by
      rcases Finset.mem_union.mp hy'.1 with ha | ha
      · have hh := Finset.mem_product.mp ha
        exact ⟨hh.1, (Finset.mem_filter.mp hh.2).1⟩
      · have hh := Finset.mem_product.mp ha
        exact ⟨(Finset.mem_filter.mp hh.1).1, hh.2⟩
    have hwy := (Finset.mem_filter.mp hs.1).2
    have hwz := (Finset.mem_filter.mp hs.2).2
    have hadj := adjacent_weights yy.1 yy.2 i hy'.2
    omega
  simp only [Emat, he, Finset.card_empty, Finset.sum_const_zero, Nat.cast_zero, mul_zero]

end DecoderResearch

namespace DecoderResearch

theorem two_neighbor_row {ℓ : ℕ} (E : Matrix (Fin (ℓ + 1)) (Fin (ℓ + 1)) ℝ)
    (K : ℝ) (hK : 0 ≤ K) (hentry : ∀ i j, E i j ≤ K)
    (hoff : ∀ i j, i.val + 1 ≠ j.val → j.val + 1 ≠ i.val → E i j = 0)
    (i : Fin (ℓ + 1)) : ∑ j, E i j ≤ 2 * K := by
  classical
  let N := Finset.univ.filter (fun j : Fin (ℓ + 1) => i.val + 1 = j.val ∨ j.val + 1 = i.val)
  have hc : N.card ≤ 2 := by
    have hi : (N.image Fin.val).card = N.card :=
      Finset.card_image_of_injective _ Fin.val_injective
    have hsub : N.image Fin.val ⊆ ({i.val - 1, i.val + 1} : Finset ℕ) := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      have hh := (Finset.mem_filter.mp hj).2
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have hp : ({i.val - 1, i.val + 1} : Finset ℕ).card = 2 :=
      Finset.card_pair (by omega)
    rw [← hi]
    exact (Finset.card_le_card hsub).trans_eq hp
  have hid : ∑ j, E i j = ∑ j ∈ N, E i j := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hj
    have hn : ¬(i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
      simpa only [N, Finset.mem_filter, Finset.mem_univ, true_and] using hj
    exact hoff i j (not_or.mp hn).1 (not_or.mp hn).2
  rw [hid]
  calc
    (∑ j ∈ N, E i j) ≤ ∑ _j ∈ N, K := Finset.sum_le_sum (fun j _ => hentry i j)
    _ = (N.card : ℝ) * K := by simp
    _ ≤ 2 * K := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hK

end DecoderResearch

open DQI.Imperfect DecoderResearch

-- This reduction retains the missing entrywise estimate as an explicit hypothesis.
-- It is not a proof of the unconditional platform target.
theorem DecoderResearch.reduction (m n ℓ : ℕ) (_hℓ : ℓ ≤ m)
    (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (dec : (Fin n → ZMod 2) → (Fin m → ZMod 2))
    (hentry : ∀ i j : Fin (ℓ + 1),
      Emat B dec ℓ i j ≤ epsMax B dec ℓ * ((m : ℝ) + 1)) :
    ∀ u : Fin (ℓ + 1) → ℝ,
      |u ⬝ᵥ (Emat B dec ℓ).mulVec u| ≤
        2 * epsMax B dec ℓ * ((m : ℝ) + 1) * (u ⬝ᵥ u) := by
  have heps : 0 ≤ epsMax B dec ℓ := by
    have he : 0 ≤ epsk B dec 0 := by unfold epsk; positivity
    exact he.trans (Finset.le_sup' (epsk B dec) (by simp : 0 ∈ Finset.range (ℓ + 1)))
  have hK : 0 ≤ epsMax B dec ℓ * ((m : ℝ) + 1) := mul_nonneg heps (by positivity)
  intro u
  have hr := two_neighbor_row (Emat B dec ℓ) _ hK hentry
    (fun i j => Emat_offdiagonal_zero B dec i j)
  simpa only [mul_assoc] using quadratic_bound (Emat B dec ℓ) _
    (Emat_nonneg B dec) (Emat_symmetric B dec) hr u

namespace DecoderCounting
open DQI.Imperfect

theorem upper_nonzero {m : ℕ} (y z : Fin m → ZMod 2) (i : Fin m)
    (h : y + z + Pi.single i 1 = 0) (hw : wt y + 1 = wt z) : z i ≠ 0 := by
  classical
  intro hz
  have hy : y i ≠ 0 := by
    have hh := congrFun h i
    simp [hz] at hh
    intro hy
    simp [hy] at hh
  have heq (j : Fin m) (hj : j ≠ i) : y j = z j := by
    have hh : y j + z j = 0 := by simpa [Pi.single_apply, hj] using congrFun h j
    simpa using eq_neg_of_add_eq_zero_left hh
  have herase : (Finset.univ.filter (fun j => y j ≠ 0)).erase i =
      (Finset.univ.filter (fun j => z j ≠ 0)).erase i := by
    ext j
    by_cases hj : j = i
    · simp [hj]
    · simp [hj, heq j hj]
  have hmy : i ∈ Finset.univ.filter (fun j => y j ≠ 0) := by simp [hy]
  have hnz : i ∉ Finset.univ.filter (fun j => z j ≠ 0) := by simp [hz]
  have hh := Finset.card_erase_add_one hmy
  rw [herase, Finset.erase_eq_of_notMem hnz] at hh
  unfold wt at hw
  omega

theorem lower_zero {m : ℕ} (y z : Fin m → ZMod 2) (i : Fin m)
    (h : y + z + Pi.single i 1 = 0) (hw : wt y + 1 = wt z) : y i = 0 := by
  have hz := upper_nonzero y z i h hw
  have hh : y i + z i + 1 = 0 := by simpa using congrFun h i
  have hb : ∀ a b : ZMod 2, b ≠ 0 → a + b + 1 = 0 → a = 0 := by decide
  exact hb _ _ hz hh

end DecoderCounting

namespace DecoderCounting
open DQI.Imperfect

theorem edge_right_card {m k : ℕ} (Y : Finset (Fin m → ZMod 2))
    (hY : ∀ z ∈ Y, wt z = k + 1) (i : Fin m) :
    (((shell m k) ×ˢ Y).filter (fun yy => yy.1 + yy.2 + Pi.single i 1 = 0)).card ≤
      (Y.filter (fun z => z i ≠ 0)).card := by
  classical
  apply Finset.card_le_card_of_injOn Prod.snd
  · intro yz hyz
    have hh := Finset.mem_filter.mp hyz
    have hm := Finset.mem_product.mp hh.1
    have hw : wt yz.1 + 1 = wt yz.2 := by
      rw [(Finset.mem_filter.mp hm.1).2, hY _ hm.2]
    exact Finset.mem_filter.mpr ⟨hm.2, upper_nonzero _ _ i hh.2 hw⟩
  · intro yz hyz y'z' hy'z' he
    have h1 := (Finset.mem_filter.mp hyz).2
    have h2 := (Finset.mem_filter.mp hy'z').2
    have hh : yz.1 + yz.2 = y'z'.1 + y'z'.2 :=
      (eq_neg_of_add_eq_zero_left h1).trans (eq_neg_of_add_eq_zero_left h2).symm
    apply Prod.ext ?_ he
    rw [he] at hh
    exact add_right_cancel hh

theorem edge_left_card {m k : ℕ} (X : Finset (Fin m → ZMod 2))
    (hX : ∀ y ∈ X, wt y = k) (i : Fin m) :
    ((X ×ˢ (shell m (k + 1))).filter (fun yy => yy.1 + yy.2 + Pi.single i 1 = 0)).card ≤
      (X.filter (fun y => y i = 0)).card := by
  classical
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro yz hyz
    have hh := Finset.mem_filter.mp hyz
    have hm := Finset.mem_product.mp hh.1
    have hw : wt yz.1 + 1 = wt yz.2 := by
      rw [hX _ hm.1, (Finset.mem_filter.mp hm.2).2]
    exact Finset.mem_filter.mpr ⟨hm.1, lower_zero _ _ i hh.2 hw⟩
  · intro yz hyz y'z' hy'z' he
    have h1 := (Finset.mem_filter.mp hyz).2
    have h2 := (Finset.mem_filter.mp hy'z').2
    have hh : yz.1 + yz.2 = y'z'.1 + y'z'.2 :=
      (eq_neg_of_add_eq_zero_left h1).trans (eq_neg_of_add_eq_zero_left h2).symm
    apply Prod.ext he
    rw [he] at hh
    exact add_left_cancel hh

theorem sum_nonzero_degrees {m k : ℕ} (Y : Finset (Fin m → ZMod 2))
    (hY : ∀ z ∈ Y, wt z = k) :
    (∑ i : Fin m, (Y.filter (fun z => z i ≠ 0)).card) = k * Y.card := by
  classical
  have hh := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := Finset.univ) (t := Y) (fun (i : Fin m) (z : Fin m → ZMod 2) => z i ≠ 0)
  change (∑ i : Fin m, (Y.filter (fun z => z i ≠ 0)).card) =
    ∑ z ∈ Y, wt z at hh
  rw [hh]
  calc
    (∑ z ∈ Y, wt z) = ∑ _z ∈ Y, k := Finset.sum_congr rfl hY
    _ = k * Y.card := by simp [mul_comm]

theorem sum_zero_degrees {m k : ℕ} (X : Finset (Fin m → ZMod 2))
    (hX : ∀ y ∈ X, wt y = k) :
    (∑ i : Fin m, (X.filter (fun y => y i = 0)).card) = (m - k) * X.card := by
  classical
  have hh := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := Finset.univ) (t := X) (fun (i : Fin m) (y : Fin m → ZMod 2) => y i = 0)
  change (∑ i : Fin m, (X.filter (fun y => y i = 0)).card) =
    ∑ y ∈ X, (Finset.univ.filter (fun i : Fin m => y i = 0)).card at hh
  rw [hh]
  have hc (y : Fin m → ZMod 2) (hy : y ∈ X) :
      (Finset.univ.filter (fun i : Fin m => y i = 0)).card = m - k := by
    have ha := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (p := fun i : Fin m => y i = 0)
    have hw := hX y hy
    simp only [Finset.card_univ, Fintype.card_fin] at ha
    change (Finset.univ.filter (fun i : Fin m => y i = 0)).card + wt y = m at ha
    omega
  rw [Finset.sum_congr rfl hc]
  simp [mul_comm]

end DecoderCounting

namespace DecoderCounting
open DQI.Imperfect

theorem failed_edge_sum {m n k : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (dec : (Fin n → ZMod 2) → (Fin m → ZMod 2)) :
    (∑ i : Fin m,
      ((((shell m k) ×ˢ (Fset B dec (k + 1))) ∪
        ((Fset B dec k) ×ˢ (shell m (k + 1)))).filter
          (fun yy => yy.1 + yy.2 + Pi.single i 1 = 0)).card) ≤
      (k + 1) * (Fset B dec (k + 1)).card + (m - k) * (Fset B dec k).card := by
  classical
  have hf (j : ℕ) (z : Fin m → ZMod 2) (hz : z ∈ Fset B dec j) : wt z = j :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2
  calc
    _ ≤ ∑ i : Fin m,
        ((Fset B dec (k + 1) |>.filter (fun z => z i ≠ 0)).card +
        (Fset B dec k |>.filter (fun y => y i = 0)).card) := by
      apply Finset.sum_le_sum
      intro i _
      rw [Finset.filter_union]
      exact (Finset.card_union_le _ _).trans
        (Nat.add_le_add (edge_right_card _ (hf (k + 1)) i) (edge_left_card _ (hf k) i))
    _ = _ := by
      rw [Finset.sum_add_distrib, sum_nonzero_degrees _ (hf (k + 1)), sum_zero_degrees _ (hf k)]

theorem balanced_normalization (a b x y : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (he : a * y = b * x) :
    2 * a * y ≤ (a + b) * Real.sqrt (x * y) := by
  have hs : Real.sqrt (x * y)^2 = x * y := Real.sq_sqrt (mul_nonneg hx hy)
  have hid : ((a + b) * Real.sqrt (x * y))^2 - (2 * a * y)^2 =
      (a - b)^2 * (x * y) := by
    rw [mul_pow (a + b), hs]
    linear_combination -4 * a * y * he
  have hpos : 0 ≤ (a + b) * Real.sqrt (x * y) := by positivity
  nlinarith [mul_nonneg (sq_nonneg (a - b)) (mul_nonneg hx hy)]

end DecoderCounting

namespace DecoderCounting
open DQI.Imperfect

theorem eps_nonneg {m n ℓ : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (dec : (Fin n → ZMod 2) → (Fin m → ZMod 2)) : 0 ≤ epsMax B dec ℓ := by
  have he : 0 ≤ epsk B dec 0 := by unfold epsk; positivity
  exact he.trans (Finset.le_sup' (epsk B dec) (by simp : 0 ∈ Finset.range (ℓ + 1)))

theorem entry_up {m n ℓ : ℕ} (hℓ : ℓ ≤ m)
    (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (dec : (Fin n → ZMod 2) → (Fin m → ZMod 2))
    (k j : Fin (ℓ + 1)) (hkj : k.val + 1 = j.val) :
    Emat B dec ℓ k j ≤ epsMax B dec ℓ * ((m : ℝ) + 1) := by
  classical
  have hk : k.val ≤ m := by omega
  have hkk : k.val + 1 ≤ m := by omega
  have hX : 0 < (Nat.choose m k.val : ℝ) := by exact_mod_cast Nat.choose_pos hk
  have hY : 0 < (Nat.choose m (k.val + 1) : ℝ) := by exact_mod_cast Nat.choose_pos hkk
  have heps := eps_nonneg (ℓ := ℓ) B dec
  have hF (r : ℕ) (hr : r ≤ ℓ) :
      ((Fset B dec r).card : ℝ) ≤ epsMax B dec ℓ * (Nat.choose m r : ℝ) := by
    have hc : 0 < (Nat.choose m r : ℝ) := by exact_mod_cast Nat.choose_pos (hr.trans hℓ)
    have hh : epsk B dec r ≤ epsMax B dec ℓ :=
      Finset.le_sup' (epsk B dec) (by simp; omega)
    exact (div_le_iff₀ hc).mp hh
  have hb : ((k.val : ℝ) + 1) * (Nat.choose m (k.val + 1) : ℝ) =
      ((m - k.val : ℕ) : ℝ) * (Nat.choose m k.val : ℝ) := by
    have hh : (k.val + 1) * Nat.choose m (k.val + 1) =
        (m - k.val) * Nat.choose m k.val := by
      simpa only [mul_comm] using Nat.choose_succ_right_eq m k.val
    exact_mod_cast hh
  have hab : (k.val : ℝ) + 1 + ((m - k.val : ℕ) : ℝ) = (m : ℝ) + 1 := by
    rw [Nat.cast_sub hk]
    ring
  have hn := balanced_normalization ((k.val : ℝ) + 1) ((m - k.val : ℕ) : ℝ)
    (Nat.choose m k.val : ℝ) (Nat.choose m (k.val + 1) : ℝ)
    (by positivity) (by positivity) hX.le hY.le hb
  rw [hab] at hn
  have hs : 0 < Real.sqrt ((Nat.choose m k.val : ℝ) * (Nat.choose m (k.val + 1) : ℝ)) :=
    Real.sqrt_pos.2 (mul_pos hX hY)
  let S : ℝ := ∑ i : Fin m,
    (((((shell m k.val) ×ˢ (Fset B dec (k.val + 1))) ∪
      ((Fset B dec k.val) ×ˢ (shell m (k.val + 1)))).filter
        (fun yy => yy.1 + yy.2 + Pi.single i 1 = 0)).card : ℝ)
  have hc : S ≤ ((k.val : ℝ) + 1) * (Fset B dec (k.val + 1)).card +
      ((m - k.val : ℕ) : ℝ) * (Fset B dec k.val).card := by
    dsimp only [S]
    exact_mod_cast (failed_edge_sum (k := k.val) B dec)
  have hb' := congrArg (fun x : ℝ => epsMax B dec ℓ * x) hb
  have hcount : S ≤ epsMax B dec ℓ * (2 * ((k.val : ℝ) + 1) * (Nat.choose m (k.val + 1) : ℝ)) := by
    have hh1 := mul_le_mul_of_nonneg_left (hF (k.val + 1) (by omega))
      (show 0 ≤ (k.val : ℝ) + 1 by positivity)
    have hh2 := mul_le_mul_of_nonneg_left (hF k.val (by omega))
      (show 0 ≤ ((m - k.val : ℕ) : ℝ) by positivity)
    nlinarith
  rw [Emat, ← hkj]
  simp only [Nat.cast_sum]
  change (1 / Real.sqrt ((Nat.choose m k.val : ℝ) * (Nat.choose m (k.val + 1) : ℝ))) * S ≤ _
  rw [one_div_mul_eq_div]
  apply (div_le_iff₀ hs).2
  have hh := mul_le_mul_of_nonneg_left hn heps
  nlinarith

theorem entry_bound {m n ℓ : ℕ} (hℓ : ℓ ≤ m)
    (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (dec : (Fin n → ZMod 2) → (Fin m → ZMod 2))
    (k j : Fin (ℓ + 1)) :
    Emat B dec ℓ k j ≤ epsMax B dec ℓ * ((m : ℝ) + 1) := by
  by_cases hkj : k.val + 1 = j.val
  · exact entry_up hℓ B dec k j hkj
  by_cases hjk : j.val + 1 = k.val
  · rw [DecoderResearch.Emat_symmetric]
    exact entry_up hℓ B dec j k hjk
  rw [DecoderResearch.Emat_offdiagonal_zero B dec k j hkj hjk]
  exact mul_nonneg (eps_nonneg B dec) (by positivity)

end DecoderCounting

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Full Lemma 10.7 of Jordan et al., arXiv:2408.08292v5.
theorem solution (m n ℓ : ℕ) (hℓ : ℓ ≤ m)
    (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (dec : (Fin n → ZMod 2) → (Fin m → ZMod 2)) :
    ∀ u : Fin (ℓ + 1) → ℝ,
      |u ⬝ᵥ (Emat B dec ℓ).mulVec u| ≤
        2 * epsMax B dec ℓ * ((m : ℝ) + 1) * (u ⬝ᵥ u) :=
  DecoderResearch.reduction m n ℓ hℓ B dec (DecoderCounting.entry_bound hℓ B dec)
