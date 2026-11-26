-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.terminalSpendSlice_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:44:04.806702+00:00
-- url     : https://prove2.me/submissions/eaeb796c-aadf-4156-97b6-70660dc3fb8f

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_normalizedReverseLift_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_realTerminalSpendTerm_nonneg
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_terminalFiber_le_choose
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_terminalPatternSet_le_choose
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_terminalPatternSet_spend_lt
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_terminalPatternSet_spend_pos
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne


attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.normalizedReverseLift_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_cons

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real NNReal
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N s r D : ℕ} (theta : ℝ)
    (hr0 : 0 < r) (hrs : r < s) :
    (∑ d ∈ terminalPatternSet N s r D,
        (terminalFiber N s r d).card *
          realTerminalPatternTerm theta r d) ≤
      ((D - 1).choose (r - 1) : ℝ) *
        ((N - D - 1).choose (s - r - 1) : ℝ) *
          realTerminalSpendTerm theta r D := by
  by_cases hempty : terminalPatternSet N s r D = ∅
  · rw [hempty]
    simp only [sum_empty]
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (realTerminalSpendTerm_nonneg theta r D)
  · obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hD0 := terminalPatternSet_spend_pos hr0 hrs.le hd
    have hDN := terminalPatternSet_spend_lt hrs hd
    have hprefixTotal : 0 < N - D := Nat.sub_pos_of_lt hDN
    have hprefixLength : 0 < s - r := Nat.sub_pos_of_lt hrs
    have hpatterns := card_terminalPatternSet_le_choose
      (N := N) (s := s) (D := D) hrs.le hD0 hr0
    have hweight : 0 ≤ realTerminalSpendTerm theta r D :=
      realTerminalSpendTerm_nonneg theta r D
    calc
      (∑ d ∈ terminalPatternSet N s r D,
          (terminalFiber N s r d).card *
            realTerminalPatternTerm theta r d) ≤
          ∑ _d ∈ terminalPatternSet N s r D,
            ((N - D - 1).choose (s - r - 1) : ℝ) *
              realTerminalSpendTerm theta r D := by
        apply sum_le_sum
        intro d hd
        have hdSum := (Finset.mem_filter.mp hd).2
        have hprefixTotalD : 0 < N - d.sum := by
          simpa [hdSum] using hprefixTotal
        have hfiber := card_terminalFiber_le_choose d
          hprefixTotalD hprefixLength
        have hfiberR :
            ((terminalFiber N s r d).card : ℝ) ≤
              ((N - D - 1).choose (s - r - 1) : ℝ) := by
          simpa [hdSum] using (show
            ((terminalFiber N s r d).card : ℝ) ≤
              (((N - d.sum - 1).choose (s - r - 1) : ℕ) : ℝ) by
                exact_mod_cast hfiber)
        have hterm :
            realTerminalPatternTerm theta r d =
              realTerminalSpendTerm theta r D := by
          simp [realTerminalPatternTerm, realTerminalSpendTerm, hdSum]
        rw [hterm]
        exact mul_le_mul_of_nonneg_right hfiberR hweight
      _ = ((terminalPatternSet N s r D).card : ℝ) *
          (((N - D - 1).choose (s - r - 1) : ℝ) *
            realTerminalSpendTerm theta r D) := by
        simp
      _ ≤ ((D - 1).choose (r - 1) : ℝ) *
          (((N - D - 1).choose (s - r - 1) : ℝ) *
            realTerminalSpendTerm theta r D) := by
        have hpatternsR :
            ((terminalPatternSet N s r D).card : ℝ) ≤
              ((D - 1).choose (r - 1) : ℝ) := by
          exact_mod_cast hpatterns
        exact mul_le_mul_of_nonneg_right hpatternsR (by positivity)
      _ = ((D - 1).choose (r - 1) : ℝ) *
          ((N - D - 1).choose (s - r - 1) : ℝ) *
            realTerminalSpendTerm theta r D := by ring
end CollatzEndpointTransport.FixedTotal
