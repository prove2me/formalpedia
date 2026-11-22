-- Prove2me | solution 1 for BooleanIsoperimetry.tailCount_succ_slice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:18.863805+00:00
-- url     : https://prove2.me/submissions/cc727596-7e2d-4f8e-9ef7-2f8aa4b1cecb

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open BooleanIsoperimetry
open Finset
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (k : ℕ) (A : Finset (Cube (N + 1))) :
    (A.filter (fun z => k ≤ z.card)).card
      = ((slice0 A).filter (fun z => k ≤ z.card)).card
        + ((slice1 A).filter (fun z => k - 1 ≤ z.card)).card := by
  -- Decompose A into the two slices as described.
  have h_decomp : A =
      Finset.image (fun x => x.image Fin.castSucc) (slice0 A) ∪
        Finset.image (fun x => insert (Fin.last N) (x.image Fin.castSucc)) (slice1 A) := by
    ext x
    constructor
    · by_cases hx : Fin.last N ∈ x
      · intro hx_A
        obtain ⟨y, hy⟩ : ∃ y : Cube N, x = insert (Fin.last N) (y.image Fin.castSucc) := by
          use Finset.filter (fun y => Fin.castSucc y ∈ x) Finset.univ
          ext y; simp
          cases y using Fin.lastCases <;> aesop
        unfold slice1; aesop
      · -- Since `Fin.last N ∉ x`, write `x = y.image Fin.castSucc` for some `y : Cube N`.
        obtain ⟨y, hy⟩ : ∃ y : Finset (Fin N), x = y.image Fin.castSucc := by
          use Finset.univ.filter (fun i => Fin.castSucc i ∈ x)
          ext i
          induction i using Fin.lastCases <;> aesop
        unfold slice0 slice1; aesop
    · unfold slice0 slice1; aesop
  conv_lhs => rw [h_decomp, Finset.filter_union]
  rw [Finset.card_union_of_disjoint, Finset.card_filter, Finset.card_filter]
  · rw [Finset.sum_image, Finset.sum_image]
    · simp +decide [Finset.card_image_of_injective _ (Fin.castSucc_injective N),
        Finset.card_insert_of_notMem]
    · intro x hx y hy
      simp +decide only [Finset.ext_iff, mem_union, mem_image, mem_insert, SetLike.mem_coe] at *
      intro h a; specialize h (Fin.castSucc a) ; aesop
    · exact fun x hx y hy hxy => Finset.image_injective (Fin.castSucc_injective _) hxy
  · simp +contextual only [disjoint_left, mem_filter, mem_image, and_true, not_exists, not_and,
      and_imp, forall_exists_index, forall_apply_eq_imp_iff₂]
    intro a ha hk x hx H; replace H := Finset.ext_iff.mp H (Fin.last N) ; simp +decide at H
end BooleanIsoperimetry
