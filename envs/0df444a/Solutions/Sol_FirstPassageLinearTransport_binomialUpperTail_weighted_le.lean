-- Prove2me | solution 1 for FirstPassageLinearTransport.binomialUpperTail_weighted_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:51:43.776055+00:00
-- url     : https://prove2.me/submissions/dc508abd-6079-41d6-8f1e-eb3f916aae9f

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Nat
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Theorems.Thm_FirstPassageLinearTransport_binomialUpperTail_eq_choose_add
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
    {r k : ℕ} (hkr : k ≤ r) (hhalf : r < 2 * k) :
    (((2 * k : ℕ) : ℝ) - (r : ℝ)) * (binomialUpperTail r k : ℝ) ≤
      (k : ℝ) * (r.choose k : ℝ) := by
  by_cases heq : k = r
  · subst k
    simp [binomialUpperTail]
    linarith
  · have hkr' : k < r := lt_of_le_of_ne hkr heq
    have hk1r : k + 1 ≤ r := by omega
    have hhalf' : r < 2 * (k + 1) := by omega
    have hrec := solution hk1r hhalf'
    have htail :
        (binomialUpperTail r k : ℝ) =
          (r.choose k : ℝ) + (binomialUpperTail r (k + 1) : ℝ) := by
      exact_mod_cast binomialUpperTail_eq_choose_add hkr
    have hchoose := congr_arg ((↑) : ℕ → ℝ)
      (Nat.choose_succ_right_eq r k)
    have htail_nonneg : 0 ≤ (binomialUpperTail r (k + 1) : ℝ) := by
      positivity
    have hcoeff :
        ((2 * k : ℕ) : ℝ) - (r : ℝ) ≤
          ((2 * (k + 1) : ℕ) : ℝ) - (r : ℝ) := by
      push_cast
      linarith
    have hstep :
        (((2 * k : ℕ) : ℝ) - (r : ℝ)) *
            (binomialUpperTail r (k + 1) : ℝ) ≤
          (((2 * (k + 1) : ℕ) : ℝ) - (r : ℝ)) *
            (binomialUpperTail r (k + 1) : ℝ) :=
      mul_le_mul_of_nonneg_right hcoeff htail_nonneg
    rw [htail]
    push_cast at hrec hchoose ⊢
    rw [Nat.cast_sub hkr] at hchoose
    nlinarith
termination_by r - k
decreasing_by omega
end FirstPassageLinearTransport
