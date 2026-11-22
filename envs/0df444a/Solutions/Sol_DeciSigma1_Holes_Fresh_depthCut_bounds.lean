-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.depthCut_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:46:21.149241+00:00
-- url     : https://prove2.me/submissions/12cd75aa-b2f9-42ab-a5ec-d70468992880

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Theorems.Thm_DeciSigma1_Holes_Fresh_depthCut_spec
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
theorem _root_.solution {t : ℕ}
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) {d : ℕ} (hd : d ≤ lowerBlockCount W t o) :
    o.2.1 ≤ depthCut W t o d ∧ depthCut W t o d ≤ o.2.2 := by
  rcases lt_or_eq_of_le hd with h | rfl
  · have h := (depthCut_spec ho).1 d h
    exact ⟨h.2.1.le, h.2.2.1⟩
  · rw [(depthCut_spec ho).2]
    exact ⟨le_rfl, (upperOcc_spec ho).1.le⟩
end DeciSigma1.Holes.Fresh
