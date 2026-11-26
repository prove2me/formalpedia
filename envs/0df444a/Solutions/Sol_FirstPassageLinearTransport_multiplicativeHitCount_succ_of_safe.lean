-- Prove2me | solution 1 for FirstPassageLinearTransport.multiplicativeHitCount_succ_of_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:57:31.918602+00:00
-- url     : https://prove2.me/submissions/459d0a2d-6002-4a7f-a6c2-a02db176e7ad

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {u z : ℝ} {r : ℕ} (hz : ¬u < z) :
    multiplicativeHitCount u (r + 1) z =
      multiplicativeHitCount u r (z * (3 / 2)) +
        multiplicativeHitCount u r (z * (1 / 2)) := by
  classical
  unfold multiplicativeHitCount
  rw [← Fintype.card_subtype
        (crossesMultiplicativeFrom u (r + 1) z),
      ← Fintype.card_subtype
        (crossesMultiplicativeFrom u r (z * (3 / 2))),
      ← Fintype.card_subtype
        (crossesMultiplicativeFrom u r (z * (1 / 2)))]
  calc
    Fintype.card
        {v : Fin (r + 1) → Bool //
          crossesMultiplicativeFrom u (r + 1) z v} =
      Fintype.card
        (Σ b : Bool,
          {w : Fin r → Bool //
            crossesMultiplicativeFrom u r
              (z * ballotMultiplier b) w}) :=
      Fintype.card_congr (safeMultiplicativeHitSuccEquiv (r := r) hz)
    _ = Fintype.card
          {w : Fin r → Bool //
            crossesMultiplicativeFrom u r (z * (3 / 2)) w} +
        Fintype.card
          {w : Fin r → Bool //
            crossesMultiplicativeFrom u r (z * (1 / 2)) w} := by
      simp only [Fintype.card_sigma, Fintype.sum_bool,
        ballotMultiplier_true, ballotMultiplier_false]
      congr 1 <;> exact Fintype.card_congr (Equiv.refl _)
end FirstPassageLinearTransport
