-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.editedTuple_visitedStates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:48:40.200006+00:00
-- url     : https://prove2.me/submissions/655599bf-7c26-483e-8e5b-64719eed2a08

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_exists_canonicalCut
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_runPrefix_canonicalCut
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Readers_Table_mem_visitedStates
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table
variable {α S : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α} {ρ : List α}
open DeciSigma1.Holes.Periodic.AdmissibleDeletion
variable {N : ℕ} {x : Piece W ρ.length → ℕ} (hx : AdmissibleDeletion W ρ N x)
include hx
namespace DeciSigma1.Holes.Periodic.AdmissibleDeletion
theorem _root_.solution [Fintype S] [DecidableEq S] (T : Table α S k)
    (hN : N = Fintype.card S)
    (l : Fin k) : T.visitedStates (editedTuple W ρ N x) l ⊆ T.visitedStates W l := by
  intro q hq
  obtain ⟨c', hc', rfl⟩ := mem_visitedStates.mp hq
  obtain ⟨c, hc⟩ := hx.exists_canonicalCut l hc'
  exact mem_visitedStates.mpr ⟨c, hc.1, (hx.runPrefix_canonicalCut T hN hc).symm⟩
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
