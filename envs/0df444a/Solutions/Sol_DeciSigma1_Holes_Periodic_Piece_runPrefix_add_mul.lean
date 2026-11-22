-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.Piece.runPrefix_add_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:42:47.115889+00:00
-- url     : https://prove2.me/submissions/cdb0693c-80cf-4d23-bb69-d97963cadb66

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Theorems.Thm_DeciSigma1_Arithmetic_runFrom_take_periodic
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_period_pos
public import Theorems.Thm_DeciSigma1_Readers_Table_runPrefix_add
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_deletePositions_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_nil
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
public import Theorems.Thm_DeciSigma1_Words_retainedCount_zero
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.deletePositions_empty
attribute [local simp] DeciSigma1.Words.deletePositions_nil
attribute [local simp] DeciSigma1.Words.greatestPreimage_empty
attribute [local simp] DeciSigma1.Words.retainedCount_empty
attribute [local simp] DeciSigma1.Words.retainedCount_greatestPreimage
attribute [local simp] DeciSigma1.Words.retainedCount_zero
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table
variable {α S : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α} {ρ : List α}
omit [DecidableEq α]
namespace DeciSigma1.Holes.Periodic
namespace Piece
theorem _root_.solution [Fintype S] (T : Table α S k) {d : ℕ} (P : Piece W d) {o m : ℕ}
    (ho : Fintype.card S * d ≤ o) (hm : o + m * (d * (Fintype.card S).factorial) ≤ P.len) :
    T.runPrefix W P.coordinate (P.start + o + m * (d * (Fintype.card S).factorial)) =
        T.runPrefix W P.coordinate (P.start + o) := by
  set u := ((W P.coordinate).drop P.start).take P.len
  have hlenu : u.length = P.len := by
    simp only [u, List.length_take, List.length_drop]; have :=
        P.stop_le_length; unfold Piece.len; omega
  have hper : Words.PeriodicOn u d 0 u.length := by
    intro p _ hp
    simp only [u, List.getElem?_take, List.getElem?_drop]
    rw [hlenu] at hp
    rw [if_pos (by omega), if_pos (by omega), ← Nat.add_assoc]
    exact P.periodic (P.start + p) (by omega) (by unfold Piece.len at hp; omega)
  have htake : ∀ t ≤ P.len, ((W P.coordinate).drop P.start).take t = u.take t := by
    intro t ht; simp only [u, List.take_take, min_eq_left ht]
  rw [Nat.add_assoc, runPrefix_add, runPrefix_add, htake _ hm, htake _ (by omega)]
  exact Arithmetic.runFrom_take_periodic T _ P.period_pos hper ho m (by omega)
end Piece
end DeciSigma1.Holes.Periodic
