-- Prove2me | solution 1 for D1Bound5.pellConvergentPair_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:55:15.03013+00:00
-- url     : https://prove2.me/submissions/6e2ded95-cf15-4e00-9c41-666e1b6cdf3b

import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellCFPrefixCheck_Definitions
import Definitions.Def_D1Bound5_PellConvergentCompleteness_Definitions

section
namespace D1Bound5



































/-- The forward recurrence that connects the short executable certificate
to the independently proved real-convergent completeness theorem. -/
theorem _root_.solution (x : ℝ) (n : ℕ) :
    pellConvergentPair x (n+2) =
      (⌊pellRealTail x (n+2)⌋ * (pellConvergentPair x (n+1)).1 +
          (pellConvergentPair x n).1,
       ⌊pellRealTail x (n+2)⌋ * (pellConvergentPair x (n+1)).2 +
          (pellConvergentPair x n).2) := by
  induction n generalizing x with
  | zero =>
      simp only [pellConvergentPair,pellRealTail]
      ext <;> ring
  | succ n ih =>
      let t := (Int.fract x)⁻¹
      change
        (⌊x⌋ * (pellConvergentPair t (n+2)).1 + (pellConvergentPair t (n+2)).2,
          (pellConvergentPair t (n+2)).1) =
        (⌊pellRealTail t (n+2)⌋ *
            (⌊x⌋ * (pellConvergentPair t (n+1)).1 + (pellConvergentPair t (n+1)).2) +
            (⌊x⌋ * (pellConvergentPair t n).1 + (pellConvergentPair t n).2),
         ⌊pellRealTail t (n+2)⌋ * (pellConvergentPair t (n+1)).1 +
            (pellConvergentPair t n).1)
      rw [ih t]
      ext <;> simp only [Prod.fst,Prod.snd] <;> ring















end D1Bound5
end
