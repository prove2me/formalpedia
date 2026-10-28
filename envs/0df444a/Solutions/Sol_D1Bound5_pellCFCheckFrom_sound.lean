-- Prove2me | solution 1 for D1Bound5.pellCFCheckFrom_sound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:33:10.463014+00:00
-- url     : https://prove2.me/submissions/b926cc49-ac15-448e-ad17-63a769bb9450

import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellCFPrefixCheck_Definitions

section
namespace D1Bound5





























theorem _root_.solution (d a0 : ℤ) (s : PellCFState) (N : ℕ)
    (h : pellCFCheckFrom d a0 s N = true) :
    (∀ i ≤ N, PellCFStateGood a0 (pellCFAt d a0 s i)) ∧
    (∀ i < N, PellCFTransitionGood d a0 (pellCFAt d a0 s i)) := by
  induction N generalizing s with
  | zero =>
      have hs : PellCFStateGood a0 s := by simpa only [pellCFCheckFrom,decide_eq_true_eq] using h
      constructor
      · intro i hi
        have hi0 : i = 0 := by omega
        simpa [hi0,pellCFAt] using hs
      · intro i hi
        omega
  | succ N ih =>
      have hh : (PellCFStateGood a0 s ∧ PellCFTransitionGood d a0 s) ∧
          pellCFCheckFrom d a0 (pellCFStep d a0 s) N = true := by
        simpa only [pellCFCheckFrom,Bool.and_eq_true,decide_eq_true_eq] using h
      obtain ⟨hg,ht⟩ := ih (pellCFStep d a0 s) hh.2
      constructor
      · intro i hi
        cases i with
        | zero => exact hh.1.1
        | succ i => exact hg i (by omega)
      · intro i hi
        cases i with
        | zero => exact hh.1.2
        | succ i => exact ht i (by omega)





















end D1Bound5
end
