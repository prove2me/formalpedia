-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.mem_upperOccurrences_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:39:18.548136+00:00
-- url     : https://prove2.me/submissions/b4ef8c81-947f-41cc-ab88-51c944a31434

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Theorems.Thm_DeciSigma1_Holes_Fresh_anchors_above_top
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_upperOcc
public import Theorems.Thm_DeciSigma1_Holes_Fresh_previousAnchor_le


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}
variable {S : Type} [Fintype S] [DecidableEq S] {T : Table α S k}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {o : Fin k × ℕ × ℕ} :
    o ∈ upperOccurrences W (topLevel W) ↔ W o.1 ≠ [] ∧ o.2.2 = (W o.1).length ∧ o.2.1 = 0 := by
  have hstart : upperOccurrenceStart W (topLevel W) o.1 (W o.1).length = 0 :=
    Nat.eq_zero_of_le_zero (previousAnchor_le fun p hp hplt => by
      rw [anchors_above_top, mem_singleton] at hp
      omega)
  rw [mem_upperOcc, anchors_above_top, mem_singleton]
  constructor
  · rintro ⟨hl, he, hs⟩
    exact ⟨hl, he, by rw [hs, he, hstart]⟩
  · rintro ⟨hl, he, hs⟩
    exact ⟨hl, he, by rw [hs, he, hstart]⟩
end DeciSigma1.Holes.Fresh
