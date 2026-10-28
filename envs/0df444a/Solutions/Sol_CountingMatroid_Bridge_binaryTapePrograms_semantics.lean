-- Prove2me | solution 1 for CountingMatroid.Bridge.binaryTapePrograms_semantics
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T19:20:04.545+00:00
-- url     : https://prove2.me/submissions/7da04faf-d1ee-4930-bf9b-cf3d64b4aa76

import Definitions.Def_CountingMatroid_Bridge_BinaryTapeSemantics
import Theorems.Thm_CountingMatroid_Bridge_binaryTapeMoveRightProgram_correct
import Theorems.Thm_CountingMatroid_Bridge_binaryTapeMoveLeftProgram_correct

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid.Bridge
open OAI.CommonBasesFPRAS

private theorem stackRead_cons_succ (b : Bool) (xs : List Bool) (i : ℕ) :
    binaryStackRead (b :: xs) (i + 1) = binaryStackRead xs i := by
  simp [binaryStackRead]

private theorem stackRead_drop_one (xs : List Bool) (i : ℕ) :
    binaryStackRead (xs.drop 1) i = binaryStackRead xs (i + 1) := by
  cases xs <;> simp [binaryStackRead]

private theorem stackRead_headD_drop_one (xs : List Bool) (i : ℕ) :
    binaryStackRead (xs.headD false :: xs.drop 1) i = binaryStackRead xs i := by
  cases xs with
  | nil => cases i <;> simp [binaryStackRead]
  | cons b tail => simp [binaryStackRead]

private theorem tapeAt_moveRight (left right : List Bool) :
    binaryTapeAt (right.headD false :: left) (right.drop 1) (.left 0) =
        binaryTapeAt left right (.right 0) ∧
    (∀ i, binaryTapeAt (right.headD false :: left) (right.drop 1) (.left (i + 1)) =
        binaryTapeAt left right (.left i)) ∧
    (∀ i, binaryTapeAt (right.headD false :: left) (right.drop 1) (.right i) =
        binaryTapeAt left right (.right (i + 1))) := by
  refine ⟨?_, ?_, ?_⟩
  · cases right <;> simp [binaryTapeAt, binaryStackRead]
  · intro i
    change binaryStackRead (right.headD false :: left) (i + 1) = binaryStackRead left i
    exact stackRead_cons_succ _ _ _
  · intro i
    change binaryStackRead (right.drop 1) i = binaryStackRead right (i + 1)
    exact stackRead_drop_one _ _

private theorem tapeAt_moveLeft (left right : List Bool) :
    (∀ i, binaryTapeAt (left.drop 1)
      (left.headD false :: (right.headD false :: right.drop 1)) (.left i) =
        binaryTapeAt left right (.left (i + 1))) ∧
    binaryTapeAt (left.drop 1)
      (left.headD false :: (right.headD false :: right.drop 1)) (.right 0) =
        binaryTapeAt left right (.left 0) ∧
    (∀ i, binaryTapeAt (left.drop 1)
      (left.headD false :: (right.headD false :: right.drop 1)) (.right (i + 1)) =
        binaryTapeAt left right (.right i)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change binaryStackRead (left.drop 1) i = binaryStackRead left (i + 1)
    exact stackRead_drop_one _ _
  · change binaryStackRead (left.headD false ::
        (right.headD false :: right.drop 1)) 0 = binaryStackRead left 0
    cases left <;> simp [binaryStackRead]
  · intro i
    change binaryStackRead (left.headD false ::
        (right.headD false :: right.drop 1)) (i + 1) = binaryStackRead right i
    rw [stackRead_cons_succ]
    exact stackRead_headD_drop_one _ _

theorem solution {n : ℕ}
    (O : IndependenceOracle n) (bits : ℕ → Bool)
    (cR : MachineConfig 0 6) (cL : MachineConfig 0 17)
    (left right : List Bool)
    (hcR : cR.control.val = 0) (hoR : cR.output = none)
    (h6R : cR.registers 6 = left) (h7R : cR.registers 7 = right)
    (hcL : cL.control.val = 0) (hoL : cL.output = none)
    (h6L : cL.registers 6 = left) (h7L : cL.registers 7 = right) :
    let outR := execution binaryTapeMoveRightProgram O cR bits 2
    let outL := execution binaryTapeMoveLeftProgram O cL bits 4
    (binaryTapeAt (outR.registers 6) (outR.registers 7) (.left 0) =
          binaryTapeAt left right (.right 0) ∧
        (∀ i, binaryTapeAt (outR.registers 6) (outR.registers 7) (.left (i + 1)) =
          binaryTapeAt left right (.left i)) ∧
        (∀ i, binaryTapeAt (outR.registers 6) (outR.registers 7) (.right i) =
          binaryTapeAt left right (.right (i + 1)))) ∧
    ((∀ i, binaryTapeAt (outL.registers 6) (outL.registers 7) (.left i) =
          binaryTapeAt left right (.left (i + 1))) ∧
        binaryTapeAt (outL.registers 6) (outL.registers 7) (.right 0) =
          binaryTapeAt left right (.left 0) ∧
        (∀ i, binaryTapeAt (outL.registers 6) (outL.registers 7) (.right (i + 1)) =
          binaryTapeAt left right (.right i))) := by
  have hR := binaryTapeMoveRightProgram_correct O bits cR left right hcR hoR h6R h7R
  have hL := binaryTapeMoveLeftProgram_correct O bits cL left right hcL hoL h6L h7L
  rcases hR with ⟨_, h6R', h7R', _, _, _⟩
  rcases hL with ⟨_, h6L', h7L', _, _, _⟩
  constructor
  · rw [h6R', h7R']
    exact tapeAt_moveRight left right
  · rw [h6L', h7L']
    exact tapeAt_moveLeft left right
