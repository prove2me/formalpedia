-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.levelCoverProperty_chainBoundFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:06:56.54783+00:00
-- url     : https://prove2.me/submissions/5bc04d58-4411-41c3-a2a9-1164d86037b2

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_WindowChains
public import Theorems.Thm_DeciSigma1_Holes_Tail_card_tailOccurrences_le
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixChain_mem_occurrences
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Tail_card_le_card_sub_one_of_injOn
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_Eligible_runPrefix_ne
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_runPrefix_ne_of_le_firstRejection
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_SuffixChain_le_length
public import Theorems.Thm_DeciSigma1_Words_SuffixChain_nodup
public import Theorems.Thm_DeciSigma1_Words_SuffixChain_prefix_of_lt
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
variable {σ : ℕ} [DecidableEq α] [Fintype S] [DecidableEq S]
omit [DecidableEq S]
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (C : LevelBounds σ k (Fintype.card S))
    {M : StructuralReader α S k} {W : Fin k → List α} {i : Fin k} {m : ℕ} (h : M.Eligible W i)
    (hK : LevelCoverProperty C m M W i) {b₀ : ℕ}
    (hb : (C.pieceCountBase + 2) * (C.chainLengthBound m + 1) ≤ b₀) :
    ChainBoundFrom (W i) b₀ (C.pieceCountBase + Fintype.card S) := by
  classical
  intro b bs hbb hbs
  have hX := C.chainLengthBound_ge_cover m
  set Q := C.pieceCountBase
  set X := C.chainLengthBound m
  set E := C.periodBound m
  set n := (W i).length with hn
  set J := M.firstRejection W i with hJ
  set B := (Q + 2) * (X + 1) with hB
  -- at most `Q + 1` occurrences of the suffix of length `B` start in the rejected tail
  have hB' : 1 + C.uncoveredBound m + (Q + 1) * (C.terminalLengthBound m + C.uncoveredBound m +
      2 * E * (Q + 1) + 1) ≤ B := by
    have e1 : 2 * E * (Q + 1) = (Q + 1) * (2 * E) := by ring
    have e2 : (Q + 1) * (C.terminalLengthBound m + C.uncoveredBound m +
        2 * E * (Q + 1) + 1) ≤ (Q + 1) * (X + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have e3 : B = (Q + 1) * (X + 1) + (X + 1) := by rw [hB]; ring
    omega
  have hocc := card_tailOccurrences_le hK.1 hK.2 hB'
  by_cases hne : bs = []
  · simp [hne]
  have hle : ∀ b' ∈ b :: bs, b' ≤ n :=
    hbs.le_length (by have := List.length_pos_of_ne_nil hne; simp; omega)
  set A := (b :: bs).toFinset with hA
  have hcard : A.card = bs.length + 1 := by
    rw [hA, List.toFinset_card_of_nodup hbs.nodup, List.length_cons]
  have hsplit := Finset.card_filter_add_card_filter_not (s := A) (p := fun b' => n - b' ≤ J)
  -- members whose suffixes start at or before the first rejected cut carry distinct live states
  have hH : (A.filter (fun b' => n - b' ≤ J)).card ≤ Fintype.card S - 1 := by
    apply card_le_card_sub_one_of_injOn _ (fun b' => n - b')
      (fun x hx y hy he => by
        rw [Finset.mem_coe, Finset.mem_filter, hA, List.mem_toFinset] at hx hy
        have := hle x hx.1; have := hle y hy.1; simp only at he; omega)
      (fun b' => M.runPrefix W i (n - b')) M.dead
    · intro x hx y hy hxy
      rw [Finset.mem_filter, hA, List.mem_toFinset] at hx hy
      have hyx : y < x := by have := hle x hx.1; have := hle y hy.1; omega
      have hpre : suffixOfLength (W i) y <+: suffixOfLength (W i) x :=
        hbs.prefix_of_lt hy.1 hx.1 hyx
      exact StructuralReader.runPrefix_ne_of_le_firstRejection h hxy hy.2 hpre
    · intro x _; exact h.runPrefix_ne _
  -- the others give distinct occurrences of the suffix of length `B` in the rejected tail
  have hT : (A.filter (fun b' => ¬ n - b' ≤ J)).card ≤ Q + 1 := by
    refine le_trans (Finset.card_le_card_of_injOn (fun b' => n - b' + b) (fun x hx => ?_)
      (fun x hx y hy he => ?_)) hocc
    · rw [Finset.mem_coe, Finset.mem_filter, hA, List.mem_toFinset] at hx
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨suffixChain_mem_occurrences hbs (hb.trans hbb) hx.1 (hle x hx.1), ?_⟩
      dsimp only
      have := hb.trans hbb
      omega
    · rw [Finset.mem_coe, Finset.mem_filter, hA, List.mem_toFinset] at hx hy
      have := hle x hx.1; have := hle y hy.1; simp only at he; omega
  omega
end DeciSigma1.Holes.Tail
