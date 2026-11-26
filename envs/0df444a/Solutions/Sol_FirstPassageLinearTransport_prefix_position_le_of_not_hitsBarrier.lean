-- Prove2me | solution 1 for FirstPassageLinearTransport.prefix_position_le_of_not_hitsBarrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:22:55.274053+00:00
-- url     : https://prove2.me/submissions/1a9b1e06-4735-4808-8301-35873c7d5363

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_Density
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_boolWalkStep_finTwo
import Theorems.Thm_FirstPassageLinearTransport_oddCount_succ_shift
import Theorems.Thm_FirstPassageLinearTransport_boolParityWord_tail
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero


attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
namespace FirstPassageLinearTransport
theorem _root_.solution :
    ∀ {r n : ℕ} {a : ℝ} {y : ℤ},
      ¬hitsBarrierFrom a r y (boolParityWord r n) →
      ∀ H : ℕ, H ≤ r →
        |(y : ℝ) + 2 * oddCount n H - H| ≤ a := by
  intro r
  induction r with
  | zero =>
      intro n a y hsafe H hHr
      have hy : ¬a < |(y : ℝ)| := by
        simpa [hitsBarrierFrom] using hsafe
      have hH : H = 0 := by omega
      subst H
      simpa using le_of_not_gt hy
  | succ r ihr =>
      intro n a y hsafe H hHr
      have hdecomp :
          ¬a < |(y : ℝ)| ∧
            ¬hitsBarrierFrom a r
              (y + boolWalkStep (boolParityWord (r + 1) n 0))
              (boolParityWord r (shortcut n)) := by
        have hraw :
            ¬a < |(y : ℝ)| ∧
              ¬hitsBarrierFrom a r
                (y + boolWalkStep (boolParityWord (r + 1) n 0))
                (fun i => boolParityWord (r + 1) n i.succ) := by
          simpa [hitsBarrierFrom] using hsafe
        simpa [boolParityWord_tail] using hraw
      rcases hdecomp with ⟨hy, htail⟩
      cases H with
      | zero => simpa using le_of_not_gt hy
      | succ H =>
          have hHr' : H ≤ r := by omega
          have hchild := ihr htail H hHr'
          rw [oddCount_succ_shift]
          have hstep := boolWalkStep_finTwo (parityBit n 0)
          change
            boolWalkStep (boolParityWord (r + 1) n 0) =
              2 * ((parityBit n 0 : ℕ) : ℤ) - 1 at hstep
          have hstepR :
              (boolWalkStep (boolParityWord (r + 1) n 0) : ℝ) =
                2 * ((parityBit n 0 : ℕ) : ℝ) - 1 := by
            exact_mod_cast hstep
          convert hchild using 1
          all_goals
            push_cast
            rw [hstepR]
            ring
end FirstPassageLinearTransport
