-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.terminalRay_admission_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:02:26.517479+00:00
-- url     : https://prove2.me/submissions/44179390-e210-459c-9f89-fb36e4750f3a

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_TerminalRays
public import Theorems.Thm_P2M_DeciSigma1_Holes_Tail_RayAgrees_getElem__ac7111bad97d
public import Theorems.Thm_DeciSigma1_Holes_Tail_rayState_eq_runPrefix
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Tail_prefix_drop_iff
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_firstRejection_le
public import Theorems.Thm_DeciSigma1_Readers_Table_pair_mem_channel
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
variable [DecidableEq α] [DecidableEq S]
namespace DeciSigma1.Holes.Tail
theorem _root_.solution {M : StructuralReader α S k} {W : Fin k → List α}
    (hW : M.IsHole W) {i j : Fin k}
    {Ωi Ωj : Ray α} (hi : RayAgrees Ωi (W i) (W i).length)
    (hj : RayAgrees Ωj (W j) (W j).length) {a b : ℕ} (hb : b ≤ M.firstRejection W j)
    (hadm : M.admitted (rayState M (M.start i) Ωi a) (rayState M (M.start j) Ωj b) = true)
    (heq : ∀ t, Ωi.stream (a + t) = Ωj.stream (b + t)) :
    ((W i).length : ℤ) + ((b : ℤ) - a + 1) ≤ (W j).length := by
  by_contra hlt
  push Not at hlt
  have hJ := StructuralReader.firstRejection_le (hW.1 j)
  have ha : a ≤ (W i).length := by omega
  rw [rayState_eq_runPrefix M hi ha, rayState_eq_runPrefix M hj (by omega)] at hadm
  have hpre : (W j).drop b <+: (W i).drop a := by
    rw [prefix_drop_iff ha]
    refine ⟨by simp; omega, fun t ht => ?_⟩
    simp only [List.length_drop] at ht
    rw [List.getElem?_drop, hi.getElem? (by omega), hj.getElem? (by omega), heq t]
  have h2 := hW.2 i j _ (pair_mem_channel ha (by omega) hpre)
  rw [h2] at hadm
  exact absurd hadm (by decide)
end DeciSigma1.Holes.Tail
