-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.depthCut_lt_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:46:45.728014+00:00
-- url     : https://prove2.me/submissions/1de4a724-64f7-4b94-827d-d4d568df19df

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Theorems.Thm_DeciSigma1_Holes_Fresh_depthCut_lt
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {W : Fin k → List α} {t : ℕ}
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) {d d' : ℕ} (hdd : d < d')
    (hd' : d' ≤ lowerBlockCount W t o) : depthCut W t o d' < depthCut W t o d := by
  induction d', hdd using Nat.le_induction with
  | base => exact depthCut_lt ho (by omega)
  | succ d' hdd ih =>
    exact (depthCut_lt ho (by omega)).trans (ih (by omega))
end DeciSigma1.Holes.Fresh
