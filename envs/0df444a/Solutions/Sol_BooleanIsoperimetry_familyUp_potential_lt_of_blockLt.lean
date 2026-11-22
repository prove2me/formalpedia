-- Prove2me | solution 1 for BooleanIsoperimetry.familyUp_potential_lt_of_blockLt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:25:48.36597+00:00
-- url     : https://prove2.me/submissions/5b1f5a3f-4e63-4dda-9813-5f19363ef1bd

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
public import Theorems.Thm_BooleanIsoperimetry_familyUpMap_injOn
public import Theorems.Thm_BooleanIsoperimetry_rank_strictMono


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {U V : Cube N} {A : Finset (Cube N)}
    (hne : familyUp U V A ≠ A)
    (hlt : ∀ S, U ⊆ S → Disjoint V S → simplicialLt (blockReplace U V S) S) :
    compressionPotential (familyUp U V A) < compressionPotential A := by
  have hsum : compressionPotential (familyUp U V A)
      = ∑ S ∈ A, rank (familyUpMap U V A S) := by
    unfold compressionPotential familyUp
    rw [Finset.sum_image]
    intro x hx y hy hxy
    exact familyUpMap_injOn U V A hx hy hxy
  rw [hsum]
  change ∑ S ∈ A, rank (familyUpMap U V A S) < compressionPotential A
  unfold compressionPotential
  apply Finset.sum_lt_sum
  · intro S _hS
    unfold familyUpMap
    split
    · next hc => exact le_of_lt (rank_strictMono (hlt S hc.1 hc.2.1))
    · exact le_rfl
  · have hex : ∃ S ∈ A, familyUpMap U V A S ≠ S := by
      by_contra hcon
      push Not at hcon
      apply hne
      unfold familyUp
      rw [Finset.image_congr (g := id) (fun S hS => hcon S hS), Finset.image_id]
    obtain ⟨S, hS, hSne⟩ := hex
    refine ⟨S, hS, ?_⟩
    unfold familyUpMap at hSne ⊢
    split at hSne
    · next hc =>
      rw [if_pos hc]
      exact rank_strictMono (hlt S hc.1 hc.2.1)
    · exact absurd rfl hSne
end BooleanIsoperimetry
