-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.exists_factor_inter_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:03:27.447191+00:00
-- url     : https://prove2.me/submissions/5c964611-685d-4833-9567-ff40cd36ff30

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_WindowChains
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Tail_card_filter_covers_le
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
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
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution {w : List α} {fs : List PeriodicFactor} {J T r x y : ℕ}
    (hunc : (uncoveredPositions fs J w.length).card ≤ T) (hJx : J ≤ x) (hy : y ≤ w.length)
    (hlen : T + fs.length * r < y - x) : ∃ f ∈ fs, r < min f.stop y - max f.start x := by
  by_contra hno
  push Not at hno
  set X := Finset.Ico x y with hX
  have hsplit := Finset.card_filter_add_card_filter_not (s := X) (p := Covers fs)
  have h1 : (X.filter (fun z => ¬ Covers fs z)).card ≤ T := by
    refine le_trans (Finset.card_le_card ?_) hunc
    intro z hz
    simp only [X, uncoveredPositions, Finset.mem_filter, Finset.mem_Ico] at hz ⊢
    exact ⟨⟨by omega, by omega⟩, hz.2⟩
  have h2 : (X.filter (Covers fs)).card ≤ fs.length * r := by
    refine (card_filter_covers_le X fs).trans ?_
    have := List.sum_le_card_nsmul
      (fs.map (fun f => (X.filter (fun z => f.start ≤ z ∧ z < f.stop)).card)) r (by
        intro c hc
        obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hc
        calc (X.filter (fun z => f.start ≤ z ∧ z < f.stop)).card
            ≤ (Finset.Ico (max f.start x) (min f.stop y)).card :=
              Finset.card_le_card (fun z hz => by
                simp only [X, Finset.mem_filter, Finset.mem_Ico] at hz ⊢; omega)
          _ = min f.stop y - max f.start x := Nat.card_Ico _ _
          _ ≤ r := hno f hf)
    simpa using this
  have h4 : X.card = y - x := Nat.card_Ico _ _
  omega
end DeciSigma1.Holes.Tail
