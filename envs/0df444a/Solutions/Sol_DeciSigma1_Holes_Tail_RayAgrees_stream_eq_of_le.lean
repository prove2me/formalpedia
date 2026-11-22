-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.RayAgrees.stream_eq_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:00:46.101012+00:00
-- url     : https://prove2.me/submissions/efd78480-f883-4861-a256-3b2488372d68

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_TerminalRays
public import Theorems.Thm_DeciSigma1_Holes_Tail_RayAgrees_stream_eq
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
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
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
namespace RayAgrees
theorem _root_.solution [DecidableEq α] {Ω Ω' : Ray α} {x : List α} {E E' : ℕ}
    (h : RayAgrees Ω x E) (h' : RayAgrees Ω' x E')
    (hE : max Ω.onset Ω'.onset + Ω.period + Ω'.period ≤ min E E')
    (t : ℕ) : Ω.stream t = Ω'.stream t := by
  simpa using Ray.stream_suffix_eq_of_prefix_eq Ω Ω' 0 0
    (fun t ht => by simpa using h.stream_eq h' (t := t) (by omega) (by omega)) t
end RayAgrees
end DeciSigma1.Holes.Tail
