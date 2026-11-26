-- Prove2me | solution 1 for FirstPassageLinearTransport.sum_bernoulliWordWeight_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:20.692074+00:00
-- url     : https://prove2.me/submissions/fa4ceb33-c664-4d92-86ec-5b06874360ce

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
theorem _root_.solution (p : ℝ) :
    ∀ r : ℕ, ∑ v : Fin r → Bool, bernoulliWordWeight p v = 1 := by
  intro r
  induction r with
  | zero => simp [bernoulliWordWeight]
  | succ r ihr =>
      rw [← Equiv.sum_comp
        (Fin.consEquiv (fun _ : Fin (r + 1) => Bool))]
      rw [Fintype.sum_prod_type]
      rw [Fintype.sum_bool]
      change
        (∑ w : Fin r → Bool, bernoulliWordWeight p (Fin.cons true w)) +
          ∑ w : Fin r → Bool, bernoulliWordWeight p (Fin.cons false w) = 1
      simp only [bernoulliWordWeight_cons, if_true, if_false]
      rw [← Finset.mul_sum, ← Finset.mul_sum, ihr]
      norm_num
end FirstPassageLinearTransport
