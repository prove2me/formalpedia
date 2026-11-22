-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.tailLengthBound_le_double_exp2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:11:44.204876+00:00
-- url     : https://prove2.me/submissions/cb35ecf8-02a9-4f8c-aec3-a55b11b6c21d

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ElementaryBound
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_LevelElementaryBound
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedForm
public import Theorems.Thm_DeciSigma1_Holes_Tail_compressionLengthBoundIter_le_log
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_add
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_mono
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_mul
public import Theorems.Thm_DeciSigma1_Arithmetic_factorial_le_exp2_sq
public import Theorems.Thm_DeciSigma1_Arithmetic_le_exp2
public import Theorems.Thm_DeciSigma1_Arithmetic_succ_le_exp2
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_coordinate
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_start
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_stop
public import Theorems.Thm_DeciSigma1_Holes_Tail_levelState_envelope
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_deletePositions_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_nil
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_empty
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_Words_pow_add
public import Theorems.Thm_DeciSigma1_Words_retainedCount_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
public import Theorems.Thm_DeciSigma1_Words_retainedCount_zero
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_coordinate
attribute [local simp] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_start
attribute [local simp] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_stop
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthBound_nil
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthEnvelope_nil
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.deletePositions_empty
attribute [local simp] DeciSigma1.Words.deletePositions_nil
attribute [local simp] DeciSigma1.Words.greatestPreimage_empty
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.Words.retainedCount_empty
attribute [local simp] DeciSigma1.Words.retainedCount_greatestPreimage
attribute [local simp] DeciSigma1.Words.retainedCount_zero
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


section
@[expose] public section
namespace DeciSigma1.Holes.Tail
open Arithmetic
private theorem uncoveredLengthBound_le_log (σ k N H : ℕ) (hH : 2 ≤ H)
    (hk : k ≤ exp2 H) (hQ : levelMultiplicity k N ≤ exp2 H)
    (hst : stateEnvelope H (levelState k N (levelCount k + 1))) :
    uncoveredLengthBound (levelBounds σ k N) ≤ exp2 (8 * H) := by
  let M := exp2 H
  have hM : 1 ≤ M := Nat.two_pow_pos H
  have hTt := hst.2.2.2.2
  rw [levelState_succ_uncoveredBound] at hTt
  have hTp : levelEscapeLength k N (levelCount k) ≤ M := by
    dsimp [M]
    nlinarith only [hTt]
  have hp : (levelState k N (levelCount k + 1)).periodBound ≤ M := hst.1
  have hu : (levelState k N (levelCount k + 1)).uncoveredBound ≤ M := hst.2.2.2.2
  have hpoly : uncoveredLengthBound (levelBounds σ k N) ≤
      M * (M + (M + 3) * (3 * M + 3) + (M + 3) * (2 * M)) := by
    unfold uncoveredLengthBound
    change k * ((levelState k N (levelCount k + 1)).uncoveredBound +
      (levelMultiplicity k N + 3) * (3 * levelEscapeLength k N (levelCount k) + 3) +
      (levelMultiplicity k N + 3) * (2 * (levelState k N (levelCount k + 1)).periodBound)) ≤ _
    gcongr
  have hpoly' : M * (M + (M + 3) * (3 * M + 3) + (M + 3) * (2 * M)) ≤
      64 * M ^ 3 := by
    have h1 : M ≤ M * M := by nlinarith
    have h2 : M * M ≤ M ^ 3 := by nlinarith
    nlinarith only [h1, h2]
  calc
    _ ≤ 64 * M ^ 3 := hpoly.trans hpoly'
    _ = exp2 (3 * H + 6) := by
      dsimp [M]
      rw [← exp2_mul]
      change exp2 6 * exp2 (H * 3) = _
      rw [← exp2_add]; congr 1; omega
    _ ≤ _ := exp2_mono (by omega)
private theorem tailLengthBound_le_raw (σ k N : ℕ) :
    tailLengthBound σ k N ≤ exp2 (exp2
      (initialLogBound k N + levelLogSlope k N * (levelCount k + 1) +
        k * (levelMultiplicity k N + 3) + 7)) := by
  let Q := levelMultiplicity k N
  let r := k * (Q + 3)
  let A := initialLogBound k N
  let B := A + levelLogSlope k N * (levelCount k + 1)
  let H := exp2 B
  have hA : k + N + Q + N * N + 20 ≤ A := by dsimp [A, initialLogBound, Q]; omega
  have hAH : A ≤ H := (by dsimp [B]; omega : A ≤ B).trans (le_exp2 B)
  have hH : 2 ≤ H := by omega
  have hN : N ≤ H := by omega
  have hN2 : N * N ≤ H := by omega
  have hkN : k * N ≤ H := by
    have : k * N ≤ A := by dsimp [A, initialLogBound]; omega
    omega
  have hr : r ≤ H := by
    have : r ≤ A := by dsimp [r, Q, A, initialLogBound]; omega
    omega
  have hs := levelState_envelope k N A (levelCount k + 1) hA
  have hlog : exp2 (levelLogSlope k N * (levelCount k + 1)) * A ≤ H := by
    calc
      _ ≤ exp2 (levelLogSlope k N * (levelCount k + 1)) * exp2 A :=
        Nat.mul_le_mul_left _ (le_exp2 A)
      _ = H := by dsimp [H, B]; rw [← exp2_add]; congr 1; omega
  have hm := exp2_mono hlog
  have hst : stateEnvelope H (levelState k N (levelCount k + 1)) :=
    ⟨hs.1.trans hm, hs.2.1.trans hm, hs.2.2.1.trans hm,
      hs.2.2.2.1.trans hm, hs.2.2.2.2.trans hm⟩
  have hE := uncoveredLengthBound_le_log σ k N H hH
    ((by omega : k ≤ H).trans (le_exp2 H))
    ((by omega : Q ≤ H).trans (le_exp2 H)) hst
  have hH8 : H ≤ 8 * H := by omega
  have hmono := exp2_mono hH8
  have hc := compressionLengthBoundIter_le_log k N
    ((levelBounds σ k N).periodBound (levelCount k)) r
    (uncoveredLengthBound (levelBounds σ k N)) (8 * H) (by omega)
    ((hN.trans (le_exp2 H)).trans hmono)
    ((factorial_le_exp2_sq N).trans (exp2_mono (hN2.trans hH8)))
    (exp2_mono ((Nat.mul_le_mul_left k (Nat.sub_le N 1)).trans (hkN.trans hH8)))
    (hst.1.trans hmono) ((hr.trans (le_exp2 H)).trans hmono) hE
  change tailLengthBound σ k N ≤ _ at hc
  apply hc.trans (exp2_mono _)
  have hr' : r + 1 ≤ exp2 r := succ_le_exp2 r
  calc
    16 * (r + 1) * (8 * H) = 128 * (r + 1) * H := by ring
    _ ≤ 128 * exp2 r * H := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hr')
    _ = exp2 (B + r + 7) := by
      change exp2 7 * exp2 r * exp2 B = _
      rw [← exp2_add, ← exp2_add]; congr 1; omega
private theorem rawExponent_le (k N : ℕ) :
    initialLogBound k N + levelLogSlope k N * (levelCount k + 1) +
      k * (levelMultiplicity k N + 3) + 7 ≤ (k + N + 20) ^ (2 * k + 5) := by
  let R := k + N + 20
  let Q := levelMultiplicity k N
  have hR : 20 ≤ R := by dsimp [R]; omega
  have hQ : Q ≤ 4 + 2 * k * N := by
    dsimp [Q, levelMultiplicity]
    gcongr <;> exact Nat.sub_le _ _
  have hQS : Q + N + 3 ≤ R ^ 2 := by
    dsimp [R]
    nlinarith only [hQ]
  have hQ' : Q ≤ R ^ 2 := by omega
  have hA : initialLogBound k N + k * (Q + 3) + 7 ≤ R ^ 4 := by
    calc
      _ ≤ k + N + R ^ 2 + N * N + k * N + 2 * k * (R ^ 2 + 3) + 27 := by
        dsimp [initialLogBound]
        change k + N + Q + N * N + k * N + k * (Q + 3) + 20 + k * (Q + 3) + 7 ≤ _
        have := Nat.mul_le_mul_left (2 * k) (Nat.add_le_add_right hQ' 3)
        nlinarith only [hQ', this]
      _ ≤ _ := by dsimp [R]; ring_nf; omega
  have hp : 1 ≤ (Q + N + 3) ^ k := Nat.one_le_pow _ _ (by omega)
  have hV : levelLogSlope k N ≤ R ^ (2 * k + 1) := by
    calc
      _ ≤ (k + N + 15) * (Q + N + 3) ^ k := by
        dsimp [levelLogSlope]
        change (k + N + 10) * (Q + N + 3) ^ k + 5 ≤ _
        nlinarith only [hp]
      _ ≤ R * (R ^ 2) ^ k :=
        Nat.mul_le_mul (by dsimp [R]; omega) (Nat.pow_le_pow_left hQS k)
      _ = _ := by rw [← pow_mul, pow_succ]; ring
  have hl : levelCount k + 1 ≤ R ^ 2 := by
    dsimp [levelCount, R]
    nlinarith
  have hprod : levelLogSlope k N * (levelCount k + 1) ≤ R ^ (2 * k + 3) := by
    calc
      _ ≤ R ^ (2 * k + 1) * R ^ 2 := Nat.mul_le_mul hV hl
      _ = _ := by rw [← pow_add]
  have h₁ : R ^ 4 ≤ R ^ (2 * k + 4) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h₂ : R ^ (2 * k + 3) ≤ R ^ (2 * k + 4) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  dsimp [Q] at hA
  calc
    _ ≤ 2 * R ^ (2 * k + 4) := by omega
    _ ≤ R * R ^ (2 * k + 4) := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by rw [show 2 * k + 5 = (2 * k + 4) + 1 by omega, pow_succ]; ring
end DeciSigma1.Holes.Tail
end
end

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open Arithmetic
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (σ k N : ℕ) :
    tailLengthBound σ k N ≤ exp2 (exp2 ((k + N + 20) ^ (2 * k + 5))) :=
  (tailLengthBound_le_raw σ k N).trans (exp2_mono (exp2_mono (rawExponent_le k N)))
end DeciSigma1.Holes.Tail
