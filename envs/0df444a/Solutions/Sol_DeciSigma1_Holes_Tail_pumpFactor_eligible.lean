-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.pumpFactor_eligible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:01:54.71623+00:00
-- url     : https://prove2.me/submissions/d26bc72d-75f2-41d1-b845-c5246e08058b

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
public import Theorems.Thm_DeciSigma1_Holes_Tail_NodeClosedAt_state
public import Theorems.Thm_DeciSigma1_Holes_Tail_length_pumpFactor
public import Theorems.Thm_DeciSigma1_Holes_Tail_pumpFactor_take
public import Theorems.Thm_DeciSigma1_Holes_Tail_pumpFactor_prefix
public import Theorems.Thm_DeciSigma1_Holes_Tail_pumpFactor_reduce_of_snoc
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_firstRejection_eq_of_rejected
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_firstRejection_spec
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_rejected_of_firstRejection_le
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_runFrom_append
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
theorem _root_.solution [DecidableEq α] (M : StructuralReader α S k)
    {W W' : Fin k → List α} {i : Fin k} {D : Finset (List α)} {c c' L : ℕ} (hW : M.Eligible W i)
    (hcl : NodeClosedAt M.toTable (M.start i) D (W i) c c') (hJ : M.firstRejection W i ≤ c)
    (hL : c' - c ≤ L) (hW' : W' i = pumpFactor (W i) c c' L) :
    M.Eligible W' i ∧ M.Immortal (M.endState W' i) ∧ M.firstRejection W' i =
        M.firstRejection W i := by
  classical
  have ⟨hcc, hc', _⟩ := hcl
  have hlen := length_pumpFactor (L := L) hcc hc'
  have hred : ∀ L', c' - c ≤ L' → ∀ p ≤ c + L', ∃ p' ≤ c', (c < p → c < p') ∧
      runFrom M.step (M.start i) ((pumpFactor (W i) c c' L').take p) =
        runFrom M.step (M.start i) ((W i).take p') := fun L' hL' =>
    pumpFactor_reduce_of_snoc (runFrom M.step (M.start i)) M.step (runFrom_snoc M.step _) hcc
      hc' hcl.state hL'
  have hq : ∀ a, M.runPrefix W' i a =
      runFrom M.step (M.start i) ((pumpFactor (W i) c c' L).take a) := by
    intro a; simp only [Table.runPrefix, hW']
  have hlive : ∀ L', c' - c ≤ L' → ∀ p ≤ c + L',
      runFrom M.step (M.start i) ((pumpFactor (W i) c c' L').take p) ≠ M.dead := by
    intro L' hL' p hp
    obtain ⟨p', hp', _, he⟩ := hred L' hL' p hp
    rw [he]
    exact hW.1 p' (by omega)
  have helig : M.Eligible W' i := by
    refine ⟨fun a ha => ?_, ?_⟩
    · rw [hq]; rw [hW', hlen] at ha; exact hlive L hL a ha
    · simp only [Table.endState, hq, hW', hlen]
      obtain ⟨p', hp', hc, he⟩ := hred L hL (c + L) le_rfl
      rw [he]
      exact StructuralReader.rejected_of_firstRejection_le hW (by have := hc (by omega); omega)
          (by omega)
  refine ⟨helig, ?_, ?_⟩
  · -- continue along longer pumped words
    intro n
    have hpre := pumpFactor_prefix (x := W i) (L := L) (L' := L + n) hcc hc' (by omega)
    have hlen' := length_pumpFactor (x := W i) (L := L + n) hcc hc'
    refine ⟨(pumpFactor (W i) c c' (L + n)).drop (c + L), by rw [List.length_drop, hlen']; omega,
      fun a ha => ?_⟩
    have hz : (pumpFactor (W i) c c' (L + n)).take (c + L) = pumpFactor (W i) c c' L := by
      obtain ⟨r, hr⟩ := hpre
      rw [← hr, List.take_left' hlen]
    have hend : M.endState W' i = runFrom M.step (M.start i) (pumpFactor (W i) c c' L) := by
      simp only [Table.endState, hq, hW', List.take_length]
    rw [hend, ← runFrom_append, ← hz, ← List.take_add]
    exact hlive (L + n) (by omega) _ (by omega)
  · apply StructuralReader.firstRejection_eq_of_rejected helig
    · rw [hq, pumpFactor_take hcc hc' hL (by omega)]
      exact (StructuralReader.firstRejection_spec hW).2.1
    · intro a' ha'
      rw [hq, pumpFactor_take hcc hc' hL (by omega)]
      exact (StructuralReader.firstRejection_spec hW).2.2 a' ha'
end DeciSigma1.Holes.Tail
