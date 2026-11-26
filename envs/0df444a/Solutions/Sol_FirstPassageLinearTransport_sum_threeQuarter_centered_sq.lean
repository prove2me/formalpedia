-- Prove2me | solution 1 for FirstPassageLinearTransport.sum_threeQuarter_centered_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:57:39.316596+00:00
-- url     : https://prove2.me/submissions/eb7f0450-b696-4363-bc89-a393cdcc2355

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_sum_bernoulliWordWeight_eq_one
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
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


attribute [local simp] FirstPassageLinearTransport.card_boolSupport_cons

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    ∀ r : ℕ,
      ∑ v : Fin r → Bool,
          bernoulliWordWeight (3 / 4) v *
            (((boolSupport v).card : ℝ) - 3 * (r : ℝ) / 4) ^ 2 =
        3 * (r : ℝ) / 16 := by
  intro r
  induction r with
  | zero => simp [bernoulliWordWeight, boolSupport]
  | succ r ihr =>
      rw [← Equiv.sum_comp
        (Fin.consEquiv (fun _ : Fin (r + 1) => Bool))]
      rw [Fintype.sum_prod_type, Fintype.sum_bool]
      simp [Fin.consEquiv, bernoulliWordWeight_cons,
        card_boolSupport_cons, Nat.cast_add, Nat.cast_succ]
      rw [← Finset.sum_add_distrib]
      calc
        (∑ w : Fin r → Bool,
            (3 / 4 * bernoulliWordWeight (3 / 4) w *
                  (1 + (↑(boolSupport w).card : ℝ) - 3 * (↑r + 1) / 4) ^ 2 +
              (1 - 3 / 4) * bernoulliWordWeight (3 / 4) w *
                  (↑(boolSupport w).card - 3 * (↑r + 1) / 4) ^ 2)) =
            (∑ w : Fin r → Bool,
              bernoulliWordWeight (3 / 4) w *
                (↑(boolSupport w).card - 3 * (r : ℝ) / 4) ^ 2) +
              (3 / 16) *
                (∑ w : Fin r → Bool, bernoulliWordWeight (3 / 4) w) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro w _hw
          ring
        _ = 3 * ((r : ℝ) + 1) / 16 := by
          rw [ihr, sum_bernoulliWordWeight_eq_one]
          norm_num
          ring
end FirstPassageLinearTransport
