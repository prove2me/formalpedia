-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.Level.next_start_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:17:37.519796+00:00
-- url     : https://prove2.me/submissions/9eb98855-ee5d-4bcd-88cd-71227ce72eaa

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Theorems.Thm_DeciSigma1_Holes_Fresh_suffix_take_iff
public import Theorems.Thm_DeciSigma1_Holes_Fresh_infix_of_occ
public import Theorems.Thm_DeciSigma1_Holes_Fresh_occ_of_suffix
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Level_lastInteriorCut_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Level_next_active
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Level_next_spec

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
open DeciSigma1.Holes.Fresh.Level
variable [DecidableEq α] (L : Level α k)
variable {L}
namespace DeciSigma1.Holes.Fresh.Level
theorem _root_.solution (hA : L.FactorAntichain) {W : Fin k → List α} (hS : L.MarkersAreSuffixes W)
    {l : Fin k}
    (hl : l ∈ (L.next W).active) :
    L.lastInteriorCut (W l) - L.blockLengthAt (W l) (L.lastInteriorCut (W l)) < (W l).length -
        (L.marker l).length := by
  obtain ⟨m, hm, hs, hlen, hl1, -, -⟩ := next_spec hl
  obtain ⟨hlact, hex⟩ := next_active.mp hl
  obtain ⟨-, hlt, -⟩ := lastInteriorCut_spec hex
  have hle : L.lastInteriorCut (W l) ≤ (W l).length := hlt.le
  have hτ := ((suffix_take_iff hle).mp hs).2
  have hσ := occ_of_suffix (hS l hlact)
  have hσl := (hS l hlact).length_le
  rw [hlen]
  by_contra hcon
  have hinf : L.marker m <:+: L.marker l := infix_of_occ hσ hτ (by omega) (by omega)
  have heq := hA.2 m hm l hlact hinf
  have : (L.marker m).length = (L.marker l).length := by rw [heq]
  omega
end DeciSigma1.Holes.Fresh.Level
