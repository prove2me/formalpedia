-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.terminalRay_no_selfAdmission
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:02:25.895962+00:00
-- url     : https://prove2.me/submissions/dbb3b8ce-011b-4bde-8d6e-788b84219d31

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
    (hW : M.IsHole W) {i : Fin k}
    {Ω : Ray α} (hΩ : RayAgrees Ω (W i) (W i).length) :
    ∀ a b, b ≤ M.firstRejection W i → a ≤ b →
      M.admitted (rayState M (M.start i) Ω a) (rayState M (M.start i) Ω b) = true →
      ¬ ∀ t, Ω.stream (a + t) = Ω.stream (b + t) := by
  intro a b hb hab hadm heq
  have hJ := StructuralReader.firstRejection_le (hW.1 i)
  rw [rayState_eq_runPrefix M hΩ (by omega), rayState_eq_runPrefix M hΩ (by omega)] at hadm
  have hpre : (W i).drop b <+: (W i).drop a := by
    rw [prefix_drop_iff (by omega)]
    refine ⟨by simp; omega, fun j hj => ?_⟩
    simp only [List.length_drop] at hj
    rw [List.getElem?_drop, hΩ.getElem? (by omega), hΩ.getElem? (by omega), heq j]
  have h2 := hW.2 i i _ (pair_mem_channel (by omega) (by omega) hpre)
  rw [h2] at hadm
  exact absurd hadm (by decide)
end DeciSigma1.Holes.Tail
