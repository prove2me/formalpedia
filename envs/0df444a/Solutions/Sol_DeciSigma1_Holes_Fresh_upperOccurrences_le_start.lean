-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.upperOccurrences_le_start
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:02:13.816545+00:00
-- url     : https://prove2.me/submissions/194dd0df-efcb-43ed-98bf-cb9f5f3b37dd

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Theorems.Thm_DeciSigma1_Holes_Fresh_le_previousAnchor
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_upperOcc

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {W : Fin k → List α} {t : ℕ} {o o' : Fin k × ℕ × ℕ}
    (ho : o ∈ upperOccurrences W t) (ho' : o' ∈ upperOccurrences W t) (h1 : o.1 = o'.1)
    (h2 : o.2.2 < o'.2.2) : o.2.2 ≤ o'.2.1 := by
  rw [(mem_upperOcc.mp ho').2.2, upperOccurrenceStart, ← h1]
  exact le_previousAnchor (mem_upperOcc.mp ho).2.1 h2
end DeciSigma1.Holes.Fresh
