-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.marker_occurrences_in_next_marker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:31:27.722969+00:00
-- url     : https://prove2.me/submissions/1c335ca8-4420-4f45-8d49-ee6ea5aa8ec1

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Theorems.Thm_DeciSigma1_Holes_Fresh_suffix_take_of_occ
public import Theorems.Thm_DeciSigma1_Holes_Fresh_occ_le_length
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Level_mem_markerEndCuts
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_ne_nil
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_eq_of_suffix
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_suffix_succ
public import Theorems.Thm_DeciSigma1_Holes_Fresh_contextAnchors_marker_succ

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
variable [DecidableEq α]
variable {W : Fin k → List α}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {t : ℕ} (ht : 1 ≤ t) {l : Fin k}
    (hl : l ∈ active W (t + 1)) :
    (∃ m ∈ active W t, marker W t m <+: marker W (t + 1) l) ∧
      marker W t l <:+ marker W (t + 1) l ∧
      ∀ h ∈ active W t, ∀ i, marker W t h <+: (marker W (t + 1) l).drop i →
        i = 0 ∨ i + (marker W t h).length = (marker W (t + 1) l).length := by
  obtain ⟨m, hm, hpre, -, hset⟩ := contextAnchors_marker_succ ht hl
  refine ⟨⟨m, hm, hpre⟩, marker_suffix_succ hl, fun h hh i hocc => ?_⟩
  have hhne := marker_ne_nil ht hh
  have hle := occ_le_length hocc hhne
  have hmem : i + (marker W t h).length ∈ contextAnchors W t (marker W (t + 1) l) := by
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    exact Level.mem_markerEndCuts.mpr ⟨hle, h, hh, suffix_take_of_occ hocc⟩
  rw [hset, mem_insert, mem_singleton] at hmem
  rcases hmem with h1 | h1
  · left
    have hs1 : marker W t h <:+ (marker W (t + 1) l).take (marker W t m).length := by
      rw [← h1]; exact suffix_take_of_occ hocc
    rw [← List.prefix_iff_eq_take.mp hpre] at hs1
    have heq := marker_eq_of_suffix hh hm hs1 List.suffix_rfl
    have : (marker W t h).length = (marker W t m).length := by rw [heq]
    omega
  · right; exact h1
end DeciSigma1.Holes.Fresh
