-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.PeriodicCover.cons_of_agree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:00:13.452225+00:00
-- url     : https://prove2.me/submissions/37ce205b-226b-4fe3-8d7b-96fce528b013

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Theorems.Thm_DeciSigma1_Holes_Tail_covers_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_transfer
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
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
namespace PeriodicCover
theorem _root_.solution {x x' : List α} {J P E T : ℕ} (h : PeriodicCover x J P E T)
    {sf : PeriodicFactor} (hsf : sf.Valid x' E) (hs : sf.start ≤ x.length)
    (hstop : sf.stop = x'.length) (hlen : x.length ≤ x'.length)
    (hagree : ∀ q < x.length, x'[q]? = x[q]?) : PeriodicCover x' J (P + 1) E T := by
  obtain ⟨fs, hfl, hfv, hunc⟩ := h
  refine ⟨sf :: fs, by simp [hfl], fun f hf => ?_, (Finset.card_le_card fun q hq => ?_).trans hunc⟩
  · rcases List.mem_cons.mp hf with rfl | hf
    · exact hsf
    · obtain ⟨hp, hpE, hfe, hper⟩ := hfv f hf
      exact ⟨hp, hpE, hfe.trans hlen, hper.transfer fun q hq => hagree q (by omega)⟩
  · simp only [uncoveredPositions, Finset.mem_filter, Finset.mem_Ico] at hq ⊢
    have hqs : q < sf.start := by
      by_contra h; exact hq.2 (covers_cons.mpr (.inl ⟨by omega, by omega⟩))
    exact ⟨⟨hq.1.1, by omega⟩, fun hc => hq.2 (covers_cons.mpr (.inr hc))⟩
end PeriodicCover
end DeciSigma1.Holes.Tail
