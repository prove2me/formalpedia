-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.take_start_append_occurrenceText
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:45:44.218341+00:00
-- url     : https://prove2.me/submissions/58c3f6a6-d4be-4686-872f-afb50cccc72f

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Theorems.Thm_DeciSigma1_Holes_Fresh_upperOcc_spec


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}
variable {S : Type} [Fintype S] [DecidableEq S] {T : Table α S k}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {t : ℕ} {o : Fin k × ℕ × ℕ}
    (ho : o ∈ upperOccurrences W t) : (W o.1).take o.2.1 ++ occurrenceText W o =
        (W o.1).take o.2.2 := by
  have h := (upperOcc_spec ho).1
  rw [occurrenceText, ← List.take_add, Nat.add_sub_cancel' h.le]
end DeciSigma1.Holes.Fresh
