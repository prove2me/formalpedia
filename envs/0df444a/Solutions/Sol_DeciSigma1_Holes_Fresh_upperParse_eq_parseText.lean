-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.upperParse_eq_parseText
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:38:25.982775+00:00
-- url     : https://prove2.me/submissions/fcd8b53f-31c8-4be6-826d-3da10fd8e80f

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Theorems.Thm_DeciSigma1_Holes_Fresh_depthCut_bounds
public import Theorems.Thm_DeciSigma1_Holes_Fresh_card_relativeCuts
public import Theorems.Thm_DeciSigma1_Holes_Fresh_depthCutAt_translate
public import Theorems.Thm_DeciSigma1_Holes_Fresh_occurrenceText_length
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_upperOcc_spec
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
attribute [local simp] DeciSigma1.Holes.Fresh.length_reversedBlocks
attribute [local simp] DeciSigma1.Holes.Fresh.length_upperSeq
attribute [local simp] DeciSigma1.Holes.Fresh.marker_zero
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_one
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_zero
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
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}
variable {S : Type} [Fintype S] [DecidableEq S] {T : Table α S k}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {t : ℕ} {o : Fin k × ℕ × ℕ}
    (ho : o ∈ upperOccurrences W t) : upperParse W t o =
        parseText (occurrenceText W o) (occurrenceCuts W t o) := by
  obtain ⟨hse, hew, he, hs, _⟩ := upperOcc_spec ho
  have hlen := occurrenceText_length ho
  have hcard : (occurrenceCuts W t o).card = lowerBlockCount W t o := card_relativeCuts _ _ _
  simp only [upperParse, reversedBlocks, parseText, hcard, hlen]
  apply congrArg List.reverse
  apply List.map_congr_left
  intro d hd
  have hd' : d < anchorCount (anchors W t o.1) o.2.1 o.2.2 := List.mem_range.mp hd
  have h1 := depthCutAt_translate hse he hs (d := d) (by omega)
  have h2 := depthCutAt_translate hse he hs (d := d + 1) (by omega)
  change ((W o.1).drop (depthCut W t o (d + 1))).take
      (depthCut W t o d - depthCut W t o (d + 1)) = _
  simp only [depthCut, h1, h2, Nat.add_sub_add_left, occurrenceText, List.drop_take, List.drop_drop,
    List.take_take, occurrenceCuts]
  congr 1
  have hbd :=
      (depthCut_bounds ho (show d ≤ lowerBlockCount W t o from Nat.le_of_lt
          (List.mem_range.mp hd))).2
  simp only [depthCut, h1] at hbd
  omega
end DeciSigma1.Holes.Fresh
