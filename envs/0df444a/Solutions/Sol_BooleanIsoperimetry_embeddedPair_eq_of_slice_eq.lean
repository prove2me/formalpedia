-- Prove2me | solution 1 for BooleanIsoperimetry.embeddedPair_eq_of_slice_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:16.521024+00:00
-- url     : https://prove2.me/submissions/e0ada051-5440-4fd0-a237-907c8ee327a8

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
public import Theorems.Thm_BooleanIsoperimetry_embeddedPair_card
public import Theorems.Thm_BooleanIsoperimetry_slice_card_add


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {A : Finset (Cube (N + 1))} {P Q : Finset (Cube N)}
    (h0 : slice0 A = P) (h1 : slice1 A = Q) :
    A = embeddedPair N P Q := by
  have h_sub : embeddedPair N (slice0 A) (slice1 A) ⊆ A := by
    intro x hx
    unfold embeddedPair at hx
    rw [Finset.mem_union] at hx
    cases hx with
    | inl h0 =>
      rw [Finset.mem_image] at h0
      rcases h0 with ⟨y, hy, hyx⟩
      unfold slice0 at hy
      rw [Finset.mem_filter] at hy
      rw [← hyx]
      exact hy.2
    | inr h1 =>
      rw [Finset.mem_image] at h1
      rcases h1 with ⟨y, hy, hyx⟩
      unfold slice1 at hy
      rw [Finset.mem_filter] at hy
      rw [← hyx]
      exact hy.2
  have h_card : (embeddedPair N (slice0 A) (slice1 A)).card = A.card := by
    rw [embeddedPair_card, slice_card_add]
  have hA : A = embeddedPair N (slice0 A) (slice1 A) :=
    (Finset.eq_of_subset_of_card_le h_sub (by rw [h_card])).symm
  rw [h0, h1] at hA
  exact hA
end BooleanIsoperimetry
