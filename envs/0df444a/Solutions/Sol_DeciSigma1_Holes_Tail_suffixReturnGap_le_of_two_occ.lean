-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.suffixReturnGap_le_of_two_occ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:52:41.37611+00:00
-- url     : https://prove2.me/submissions/e0d1852c-0e3d-4f0f-845a-a4feee609569

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffix_take_iff
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_Words_mem_occurrences
public import Theorems.Thm_DeciSigma1_Words_suffixReturnGap_le_of_occ
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
public import Theorems.Thm_P2M_DeciSigma1_Holes_Tail_getElem__suffixOfLength_5cd134b71b98
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthBound_nil
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthEnvelope_nil

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Words
variable {α S : Type} {k : ℕ}
variable [DecidableEq α] [Fintype S]
namespace DeciSigma1.Holes.Tail
theorem _root_.solution {x t : List α} {b g e e' : ℕ}
    (he : e ∈ occurrences x t (b + g))
    (he' : e' ∈ occurrences x t b) (hlt : e' < e) (hgap : e - e' ≤ g) :
    ∃ h, suffixReturnGap t b = some h ∧ h ≤ e - e' := by
  rw [mem_occurrences] at he he'
  obtain ⟨hex, hbt, hocc⟩ := he
  obtain ⟨hex', hbt', hocc'⟩ := he'
  have hl1 : (suffixOfLength t (b + g)).length = b + g := by simp [hbt]
  have hl2 : (suffixOfLength t b).length = b := by simp [hbt']
  rw [suffix_take_iff hex, hl1] at hocc
  rw [suffix_take_iff hex', hl2] at hocc'
  obtain ⟨hbe, hocc⟩ := hocc
  obtain ⟨hbe', hocc'⟩ := hocc'
  apply suffixReturnGap_le_of_occ hbt' (by omega) (by omega)
  rw [suffix_take_iff (by omega), hl2]
  refine ⟨by omega, fun j hj => ?_⟩
  have e1 := hocc (b + g - (e - e') - b + j) (by omega)
  have e2 := hocc' j hj
  rw [getElem?_suffixOfLength] at e1 e2 ⊢
  rw [← e2, show t.length - (e - e') - b + j = t.length - (b + g) + (b + g - (e - e') - b + j) by
    omega, ← e1]
  congr 1; omega
end DeciSigma1.Holes.Tail
