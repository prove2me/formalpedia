-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.repeatFactorRay_period
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:01:23.195272+00:00
-- url     : https://prove2.me/submissions/057d8896-aa5d-471a-8ed1-b004a652b0a9

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_TerminalRays
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayCompatibility
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Holes_Tail_pumpFactor_letter_period
public import Theorems.Thm_DeciSigma1_Holes_Tail_streamPrefix_repeatFactorRay
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthBound_nil
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthEnvelope_nil
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Arithmetic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
variable {T : Table α S k} {q0 : S} {x : List α} {B c c' : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (hcl : ClosedAt T q0 x B c c') :
    ∀ p, c - B ≤ p → (repeatFactorRay x c c' hcl.2.1 hcl.2.2.1).stream (p + (c' - c)) =
      (repeatFactorRay x c c' hcl.2.1 hcl.2.2.1).stream p := by
  intro p hp
  have hcc := hcl.2.1; have hc' := hcl.2.2.1
  have hpre := streamPrefix_repeatFactorRay hcc hc' (p + (c' - c) + 1)
  have h1 := pumpFactor_letter_period hcl (L := p + (c' - c) + 1) (by omega) hp (by omega)
  rw [← hpre, List.getElem?_eq_getElem (by simp; omega),
    List.getElem?_eq_getElem (by simp; omega), getElem_streamPrefix _ _ _ (by omega),
    getElem_streamPrefix _ _ _ (by omega)] at h1
  exact (Option.some.inj h1).symm
end DeciSigma1.Holes.Tail
