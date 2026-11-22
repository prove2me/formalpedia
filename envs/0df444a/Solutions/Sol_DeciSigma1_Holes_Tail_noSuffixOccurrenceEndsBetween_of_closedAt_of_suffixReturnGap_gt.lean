-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.noSuffixOccurrenceEndsBetween_of_closedAt_of_suffixReturnGap_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:51:22.427789+00:00
-- url     : https://prove2.me/submissions/91f1fff3-74c7-4d92-bd98-2f5d03110ec3

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffix_take_iff
public import Theorems.Thm_P2M_DeciSigma1_Holes_Tail_getElem__suffixOfLength_5cd134b71b98
public import Theorems.Thm_DeciSigma1_Holes_Tail_ClosedAt_window
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_Words_mem_occurrences
public import Theorems.Thm_DeciSigma1_Words_suffixReturnGap_le_of_occ
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers
open DeciSigma1.Words (pow)
open DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution [DecidableEq α]
    {T : Table α S k} {q0 : S}
    {x t : List α} {B B' c c' : ℕ}
    (hcl : ClosedAt T q0 x B' c c') (hB : B + (c' - c) ≤ B')
    (hD : ∀ h,
        Words.suffixReturnGap t B = some h → c' - c <
            h) : NoSuffixOccurrenceEndsBetween x t B' c c' := by
  intro e he
  by_contra hcon
  push Not at hcon
  have ⟨hB', hcc, hc', _⟩ := hcl
  rw [Words.mem_occurrences] at he
  obtain ⟨hex, hBt, hocc⟩ := he
  have hlen' : (Words.suffixOfLength t B').length = B' := by simp [hBt]
  rw [suffix_take_iff hex, hlen'] at hocc
  obtain ⟨hBe, hocc⟩ := hocc
  set h := c' - c with hh
  -- `v_B(t)` occurs in `t` ending at distance `h` from its end
  have hocc2 : Words.suffixOfLength t B <:+ t.take (t.length - h) := by
    rw [suffix_take_iff (by omega)]
    simp only [Words.length_suffixOfLength, min_eq_left (by omega : B ≤ t.length)]
    refine ⟨by omega, fun j hj => ?_⟩
    have e1 := hocc (B' - h - B + j) (by omega)
    have e2 := hocc (B' - B + j) (by omega)
    have e3 := hcl.window (j := e - h - B + j - (c - B')) (by omega)
    rw [getElem?_suffixOfLength] at e1 e2
    rw [getElem?_suffixOfLength]
    have i1 : t.length - h - B + j = t.length - B' + (B' - h - B + j) := by omega
    have i2 : t.length - B + j = t.length - B' + (B' - B + j) := by omega
    rw [i1, i2, ← e1, ← e2]
    have i3 : e - B' + (B' - h - B + j) = c - B' + (e - h - B + j - (c - B')) := by omega
    have i4 : e - B' + (B' - B + j) = c' - B' + (e - h - B + j - (c - B')) := by omega
    rw [i3, i4]
    exact e3
  obtain ⟨h0, hD0, hle⟩ := Words.suffixReturnGap_le_of_occ (by omega) (by omega) (by omega) hocc2
  have := hD h0 hD0
  omega
end DeciSigma1.Holes.Tail
