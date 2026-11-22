-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.levelStep_envelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:08:39.632911+00:00
-- url     : https://prove2.me/submissions/23a091cd-ce11-4eb7-8d5b-631f959ac913

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_ElementaryBounds
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_LevelElementaryBound
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_le_exp2
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_add
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_mono
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_mul
public import Theorems.Thm_DeciSigma1_Arithmetic_factorial_le_exp2_sq
public import Theorems.Thm_DeciSigma1_Arithmetic_le_exp2
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
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


section
@[expose] public section
namespace DeciSigma1.Holes.Tail
open Arithmetic
private theorem exp2_pos (t : ℕ) : 0 < exp2 t := by
  exact Nat.two_pow_pos t
private theorem levelStep_polynomial (k N Q M : ℕ) (st : LevelState)
    (hM : 1 ≤ M) (hN : N ≤ M) (hQ : Q ≤ M) (hfac : N.factorial ≤ M)
    (hst : st.periodBound ≤ M ∧ st.chainLengthBound ≤ M ∧
      st.previousChainLengthBound ≤ M ∧ st.terminalLengthBound ≤ M ∧
      st.uncoveredBound ≤ M)
    (hTp : suffixLengthBound k N (List.replicate k (Q + N))
      (levelStartWindow N Q st) ≤ M) :
    (levelStep k N Q st).periodBound ≤ 64 * M ^ 3 ∧
    (levelStep k N Q st).chainLengthBound ≤ 64 * M ^ 3 ∧
    (levelStep k N Q st).previousChainLengthBound ≤ 64 * M ^ 3 ∧
    (levelStep k N Q st).terminalLengthBound ≤ 64 * M ^ 3 ∧
    (levelStep k N Q st).uncoveredBound ≤ 64 * M ^ 3 := by
  let Tp := suffixLengthBound k N (List.replicate k (Q + N)) (levelStartWindow N Q st)
  let e := max (factorLengthBound k N (suffixLengthEnvelope k N
    (List.replicate k (Q + N)) (levelStartWindow N Q st))) st.periodBound
  have he : e ≤ M := max_le
    ((Nat.le_of_lt (factorLengthBound_suffixLengthEnvelope_lt _ _ _ _)).trans hTp) hst.1
  have hchain : (levelStep k N Q st).chainLengthBound ≤
      (M + 2) * (1 + 2 * M) + (M + 2) * (3 * M + 3) +
        ((1 + (M + M) * (M * M)) + 2 * (M * M) + M * M +
          (M + 3) * (3 * M) + M + M) + M := by
    change (Q + 2) * (1 + 2 * e) + (Q + 2) * (3 * Tp + 3) +
      ((1 + (st.chainLengthBound + N) * (e * N.factorial)) +
        2 * (e * N.factorial) + N * e + (Q + 3) * (3 * e) +
        st.uncoveredBound + st.terminalLengthBound) + N ≤ _
    gcongr <;> first | exact hst.2.1 |
      exact hst.2.2.2.1 | exact hst.2.2.2.2
  have hpoly : (M + 2) * (1 + 2 * M) + (M + 2) * (3 * M + 3) +
        ((1 + (M + M) * (M * M)) + 2 * (M * M) + M * M +
          (M + 3) * (3 * M) + M + M) + M ≤ 64 * M ^ 3 := by
    have h1 : M ≤ M * M := by nlinarith
    have h2 : M * M ≤ M ^ 3 := by nlinarith
    nlinarith only [hM, h1, h2]
  have hbound := hchain.trans hpoly
  have hsmall : M ≤ 64 * M ^ 3 := by
    have := Nat.pow_le_pow_right hM (by decide : 1 ≤ 3)
    simp only [pow_one] at this
    omega
  refine ⟨he.trans hsmall, hbound, hst.2.1.trans hsmall, ?_, ?_⟩
  · exact (by dsimp [levelStep]; omega :
      (levelStep k N Q st).terminalLengthBound ≤ (levelStep k N Q st).chainLengthBound).trans
        hbound
  · exact (by dsimp [levelStep]; omega :
      (levelStep k N Q st).uncoveredBound ≤ (levelStep k N Q st).chainLengthBound).trans
        hbound
end DeciSigma1.Holes.Tail
end
end

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open Arithmetic
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (k N Q H : ℕ) {st : LevelState}
    (hH : k + N + Q + N * N + 20 ≤ H) (hst : stateEnvelope H st) :
    stateEnvelope (exp2 ((k + N + 10) * (Q + N + 3) ^ k + 5) * H)
      (levelStep k N Q st) := by
  have hpos : 1 ≤ H := by omega
  have hN : N ≤ exp2 H := (by omega : N ≤ H).trans (le_exp2 H)
  have hQ : Q ≤ exp2 H := (by omega : Q ≤ H).trans (le_exp2 H)
  have hwindow : levelStartWindow N Q st + 2 ≤ exp2 (4 * H) := by
    have hN1 : N + 1 ≤ exp2 H := (by omega : N + 1 ≤ H).trans (le_exp2 H)
    have hQ2 : Q + 2 ≤ exp2 H := (by omega : Q + 2 ≤ H).trans (le_exp2 H)
    have hb : levelStartWindow N Q st + 2 ≤
        exp2 H * exp2 H + exp2 H * (exp2 H + 1) + 2 := by
      unfold levelStartWindow
      gcongr
      · exact hst.1
      · exact hst.2.2.1
    have hE : 2 ≤ exp2 H := exp2_mono hpos
    have hmul : exp2 H * exp2 H = exp2 (2 * H) := by
      rw [← exp2_add]; congr 1; omega
    have hlow : exp2 H ≤ exp2 (2 * H) := exp2_mono (by omega)
    have hb' : levelStartWindow N Q st + 2 ≤ exp2 (2 * H + 2) := by
      rw [exp2_add]
      change _ ≤ exp2 (2 * H) * 4
      nlinarith only [hb, hmul, hlow, hE]
    exact hb'.trans (exp2_mono (by omega))
  let C := exp2 ((k + N + 10) * (Q + N + 3) ^ k)
  let T := C * (4 * H)
  have hC : 1 ≤ C := exp2_pos _
  have hHT : H ≤ T := by dsimp [T]; nlinarith
  have hT : 2 ≤ T := by dsimp [T]; nlinarith
  have hm := exp2_mono hHT
  have hTp := suffixLengthBound_le_exp2 k N (Q + N) k _ _ hwindow
  have hp := levelStep_polynomial k N Q (exp2 T) st (exp2_pos _)
    (hN.trans hm) (hQ.trans hm)
    ((factorial_le_exp2_sq N).trans (exp2_mono (by omega)))
    ⟨hst.1.trans hm, hst.2.1.trans hm, hst.2.2.1.trans hm,
      hst.2.2.2.1.trans hm, hst.2.2.2.2.trans hm⟩
    (by exact (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans hTp))
  have hlast : 64 * exp2 T ^ 3 ≤
      exp2 (exp2 ((k + N + 10) * (Q + N + 3) ^ k + 5) * H) := by
    calc
      _ = exp2 (3 * T + 6) := by
        rw [← exp2_mul]
        change exp2 6 * exp2 (T * 3) = _
        rw [← exp2_add]; congr 1; omega
      _ ≤ _ := by
        apply exp2_mono
        rw [exp2_add]
        change 3 * T + 6 ≤ (C * 32) * H
        dsimp [T] at *
        nlinarith only [hT]
  exact ⟨hp.1.trans hlast, hp.2.1.trans hlast, hp.2.2.1.trans hlast,
    hp.2.2.2.1.trans hlast, hp.2.2.2.2.trans hlast⟩
end DeciSigma1.Holes.Tail
