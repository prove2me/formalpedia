-- Prove2me | solution 1 for BooleanIsoperimetry.cubeToNat_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:00.79784+00:00
-- url     : https://prove2.me/submissions/35e910b6-332c-4617-add1-cb09adcfceec

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff
section
@[expose] public section
open scoped BigOperators
namespace BooleanIsoperimetry
private lemma ofDigits_map_eq_sum (n : ℕ) (S : Finset ℕ) :
    Nat.ofDigits 2 (List.map (fun i => if i ∈ S then 1 else 0) (List.range n)) =
    ∑ i ∈ Finset.range n, (if i ∈ S then 2^i else 0) := by
  induction n with
  | zero =>
      simp
  | succ m ih =>
      simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
        Nat.ofDigits_append, List.length_map, List.length_range, Nat.ofDigits_singleton,
        mul_ite, mul_one, mul_zero, Finset.range_add_one, Finset.sum_insert,
        Finset.mem_range, lt_self_iff_false, not_false_eq_true, ih]
      by_cases hm : m ∈ S <;> simp [hm]
      ring
end BooleanIsoperimetry
end
end

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} {x y : Cube n} (h : cubeToNat x = cubeToNat y) : x = y := by
  revert x y
  have h_unique_binary :
      ∀ {x y : Finset ℕ}, x ⊆ Finset.range n → y ⊆ Finset.range n →
        (∑ i ∈ x, 2^i) = (∑ i ∈ y, 2^i) → x = y := by
    intros x y hx hy hsum_eq
    have h_binary_eq :
        (Nat.ofDigits 2 (List.map (fun i => if i ∈ x then 1 else 0) (List.range n))) =
          (Nat.ofDigits 2 (List.map (fun i => if i ∈ y then 1 else 0) (List.range n))) := by
      have h_binary_eq :
          (∑ i ∈ Finset.range n, (if i ∈ x then 2^i else 0)) =
            (∑ i ∈ Finset.range n, (if i ∈ y then 2^i else 0)) := by
        simp_all +decide only [Finset.sum_ite_mem]
        rw [Finset.inter_eq_right.mpr hx, Finset.inter_eq_right.mpr hy, hsum_eq]
      rw [ofDigits_map_eq_sum n x, ofDigits_map_eq_sum n y]
      exact h_binary_eq
    have h_binary_eq :
        List.map (fun i => if i ∈ x then 1 else 0) (List.range n) =
          List.map (fun i => if i ∈ y then 1 else 0) (List.range n) := by
      -- Little-endian binary representation is injective on bit lists of equal length.
      have h_ofDigits_inj :
          ∀ {l1 l2 : List ℕ}, (∀ i ∈ l1, i = 0 ∨ i = 1) →
            (∀ i ∈ l2, i = 0 ∨ i = 1) → List.length l1 = List.length l2 →
            Nat.ofDigits 2 l1 = Nat.ofDigits 2 l2 → l1 = l2 := by
        intro l1
        induction l1 with
        | nil =>
            intro l2 hl1 hl2 hlen hsum_eq
            cases l2 with
            | nil => rfl
            | cons d2 l2 => simp at hlen
        | cons d1 l1 ih =>
            intro l2 hl1 hl2 hlen hsum_eq
            cases l2 with
            | nil => simp at hlen
            | cons d2 l2 =>
                simp only [Nat.ofDigits, List.cons.injEq] at hsum_eq ⊢
                have hd1 : d1 = 0 ∨ d1 = 1 := hl1 d1 (by simp)
                have hd2 : d2 = 0 ∨ d2 = 1 := hl2 d2 (by simp)
                have htail_len : l1.length = l2.length := by simpa using hlen
                have htail_bits1 : ∀ i ∈ l1, i = 0 ∨ i = 1 := by
                  intro i hi
                  exact hl1 i (by simp [hi])
                have htail_bits2 : ∀ i ∈ l2, i = 0 ∨ i = 1 := by
                  intro i hi
                  exact hl2 i (by simp [hi])
                rcases hd1 with rfl | rfl <;> rcases hd2 with rfl | rfl
                all_goals
                  have htail_sum : Nat.ofDigits 2 l1 = Nat.ofDigits 2 l2 := by omega
                  exact ⟨ by omega, ih htail_bits1 htail_bits2 htail_len htail_sum ⟩
      exact h_ofDigits_inj
        (fun i hi => by
          rw [List.mem_map] at hi
          rcases hi with ⟨i, _, rfl⟩
          by_cases hi' : i ∈ x <;> simp +decide [hi'])
        (fun i hi => by
          rw [List.mem_map] at hi
          rcases hi with ⟨i, _, rfl⟩
          by_cases hi' : i ∈ y <;> simp +decide [hi'])
        (by simp +decide) ‹_›
    simp_all +decide
    grind
  intro x y hxy
  specialize @h_unique_binary (Finset.image (fun i : Fin n => (i : ℕ)) x)
    (Finset.image (fun i : Fin n => (i : ℕ)) y)
  simp_all +decide only [Finset.subset_iff, Finset.mem_image, Finset.mem_range,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Fin.is_lt, implies_true,
    forall_const]
  simp_all +decide only [Fin.val_injective.eq_iff, implies_true,
    Set.injOn_of_eq_iff_eq, Finset.sum_image]
  exact Finset.image_injective (fun a b h => by simpa [Fin.ext_iff] using h)
    (h_unique_binary hxy)
end BooleanIsoperimetry
