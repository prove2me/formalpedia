-- Prove2me | solution 1 for BooleanIsoperimetry.rank_add_min_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:53.595675+00:00
-- url     : https://prove2.me/submissions/b8c6f07f-d746-442c-acd4-f0f3fd07f4e1

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_cubeToNat_erase
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} (w : Cube n) (h : w.Nonempty) :
    n ≤ rank w + (w.min' h : ℕ) := by
  classical
  -- By definition of $f$, we know that for any $c$ in the set
  -- $\{c : Fin n \mid (w.min' h : ℕ) \leq c\}$, $f(c)$ is in the set $\{y \mid simplicialLt y w\}$.
  have h_f_image : Finset.image
      (fun c => if c ∈ w then w.erase c else insert c (w.erase (w.min' h)))
      (Finset.filter (fun c => (w.min' h : ℕ) ≤ c) Finset.univ) ⊆
      Finset.univ.filter (fun y => simplicialLt y w) := by
    intro
    simp +zetaDelta only [Fin.val_fin_le, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, forall_exists_index, and_imp] at *
    rintro x hx rfl; split_ifs <;> simp_all +decide only [simplicialLt]
    · simp +decide [simplicialLe, *]
      grind +qlia
    · constructor <;>
        simp_all +decide only [simplicialLe, Finset.mem_erase, ne_eq, and_false,
          not_false_eq_true, Finset.card_insert_of_notMem, Order.lt_add_one_iff, not_or, not_le,
          not_and]
      · refine Or.inr ⟨ ?_, ?_ ⟩
        · rw [Finset.card_erase_add_one (Finset.min'_mem _ h)]
        · rw [cubeToNat, cubeToNat]
          rw [← Finset.sum_erase_add _ _ (Finset.min'_mem _ h), add_comm]
          rw [Finset.sum_insert] <;> norm_num
          · exact pow_le_pow_right₀ (by decide) hx
          · tauto
      · constructor
        · exact Finset.card_lt_card (Finset.erase_ssubset (Finset.min'_mem _ h) )
        · intro h_card
          have h_cubeToNat : cubeToNat w = cubeToNat (w.erase (w.min' h)) + 2 ^ (w.min' h : ℕ) := by
            exact cubeToNat_erase (Finset.min'_mem _ h)
          have h_cubeToNat_insert : cubeToNat (insert x (w.erase (w.min' h))) =
              cubeToNat (w.erase (w.min' h)) + 2 ^ (x : ℕ) := by
            unfold cubeToNat; simp +decide [*, Finset.sum_insert]
            ring
          cases lt_or_eq_of_le hx <;> simp_all +decide [pow_lt_pow_iff_right₀]
  have h_f_card : Finset.card (Finset.image
      (fun c => if c ∈ w then w.erase c else insert c (w.erase (w.min' h)))
      (Finset.filter (fun c => (w.min' h : ℕ) ≤ c) Finset.univ)) ≥ n - (w.min' h : ℕ) := by
    rw [Finset.card_image_of_injOn]
    · simp_all +decide [Finset.filter_le_eq_Ici]
    · intro x hx y hy; simp_all +decide only [Fin.val_fin_le, Finset.coe_filter,
        Finset.mem_univ, true_and, Set.mem_ofPred_eq, Finset.ext_iff]
      intro h; have := h x; have := h y
      split_ifs at * <;> simp_all +decide [Finset.mem_erase, Finset.mem_insert]
      grind
  have := Finset.card_le_card h_f_image; simp_all +decide [rank]
  grind
end BooleanIsoperimetry
