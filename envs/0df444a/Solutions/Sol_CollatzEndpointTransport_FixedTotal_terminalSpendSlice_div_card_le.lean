-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.terminalSpendSlice_div_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:45:13.383279+00:00
-- url     : https://prove2.me/submissions/99fcb5c7-e21b-49ae-b024-f2bd6f187960

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
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_terminalSpendSlice_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_fixedSet
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_terminalPatternSet_spend_bounds
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_terminalPatternSet_spend_lt
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_terminalPatternSet_spend_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_terminal_choose_ratio_le
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
    (hN : 1 < N) (hs1 : 1 < s) (hsN : s < N)
    (hr0 : 0 < r) (hrs : r < s) :
    (∑ d ∈ terminalPatternSet N s r D,
        (terminalFiber N s r d).card *
          realTerminalPatternTerm theta r d) /
          ((fixedSet N s).card : ℝ) ≤
      (N : ℝ) *
        centralSeparatorProportion N s ^ r *
        (1 - centralSeparatorProportion N s) ^ (D - r) *
        ((D - 1).choose (r - 1) : ℝ) *
        realTerminalSpendTerm theta r D := by
  have hcard : 0 < ((fixedSet N s).card : ℝ) := by
    rw [card_fixedSet N s (by omega) (by omega)]
    exact_mod_cast Nat.choose_pos (by omega : s - 1 ≤ N - 1)
  have hpi0 : 0 ≤ centralSeparatorProportion N s := by
    unfold centralSeparatorProportion
    positivity
  have hpi1 : centralSeparatorProportion N s ≤ 1 := by
    unfold centralSeparatorProportion
    have hNm1 : 0 < (N - 1 : ℕ) := by omega
    apply (div_le_one (by exact_mod_cast hNm1 : (0 : ℝ) < (N - 1 : ℕ))).2
    exact_mod_cast (by omega : s - 1 ≤ N - 1)
  have hq0 : 0 ≤ 1 - centralSeparatorProportion N s := sub_nonneg.mpr hpi1
  by_cases hempty : terminalPatternSet N s r D = ∅
  · rw [hempty]
    simp only [sum_empty, zero_div]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (Nat.cast_nonneg N) (pow_nonneg hpi0 _))
          (pow_nonneg hq0 _))
        (Nat.cast_nonneg _))
      (realTerminalSpendTerm_nonneg theta r D)
  · obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hD0 := terminalPatternSet_spend_pos hr0 hrs.le hd
    have hDN := terminalPatternSet_spend_lt hrs hd
    obtain ⟨hrD, hprefixSpend⟩ :=
      terminalPatternSet_spend_bounds hrs.le hd
    have hratio := terminal_choose_ratio_le
      (n := N - 1) (k := s - 1) (D := D) (r := r)
      (by omega) (by omega) (by omega) (by omega) hrD (by omega)
    have hprefixIndex :
        (N - 1 - D).choose (s - 1 - r) =
          (N - D - 1).choose (s - r - 1) := by
      congr 1 <;> omega
    have htotalIndex :
        (N - 1).choose (s - 1) = (fixedSet N s).card := by
      rw [card_fixedSet N s (by omega) (by omega)]
    have hq :
        (((N - 1 - (s - 1) : ℕ) : ℝ) / (N - 1 : ℕ)) =
          1 - centralSeparatorProportion N s := by
      rw [show N - 1 - (s - 1) = N - s by omega]
      unfold centralSeparatorProportion
      rw [Nat.cast_sub hsN.le, Nat.cast_sub (by omega : 1 ≤ N),
        Nat.cast_sub (by omega : 1 ≤ s)]
      have hNreal : (1 : ℝ) < N := by exact_mod_cast hN
      field_simp [show (N : ℝ) - 1 ≠ 0 by linarith]
      ring
    rw [hprefixIndex, htotalIndex, hq] at hratio
    have hratio' :
        ((N - D - 1).choose (s - r - 1) : ℝ) /
            ((fixedSet N s).card : ℝ) ≤
          (N : ℝ) * centralSeparatorProportion N s ^ r *
            (1 - centralSeparatorProportion N s) ^ (D - r) := by
      simpa [centralSeparatorProportion,
        Nat.cast_sub (by omega : 1 ≤ N),
        Nat.cast_sub (by omega : 1 ≤ s)] using hratio
    have hprefixBound :
        ((N - D - 1).choose (s - r - 1) : ℝ) ≤
          ((N : ℝ) * centralSeparatorProportion N s ^ r *
            (1 - centralSeparatorProportion N s) ^ (D - r)) *
              ((fixedSet N s).card : ℝ) :=
      (div_le_iff₀ hcard).mp hratio'
    have hslice := terminalSpendSlice_le
      (N := N) (s := s) (r := r) (D := D) theta hr0 hrs
    apply (div_le_iff₀ hcard).2
    calc
      (∑ d ∈ terminalPatternSet N s r D,
          (terminalFiber N s r d).card *
            realTerminalPatternTerm theta r d) ≤
          ((D - 1).choose (r - 1) : ℝ) *
            ((N - D - 1).choose (s - r - 1) : ℝ) *
              realTerminalSpendTerm theta r D := hslice
      _ ≤ ((D - 1).choose (r - 1) : ℝ) *
          ((N : ℝ) * centralSeparatorProportion N s ^ r *
            (1 - centralSeparatorProportion N s) ^ (D - r) *
              ((fixedSet N s).card : ℝ)) *
            realTerminalSpendTerm theta r D := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hprefixBound (Nat.cast_nonneg _))
          (realTerminalSpendTerm_nonneg theta r D)
      _ = ((N : ℝ) * centralSeparatorProportion N s ^ r *
          (1 - centralSeparatorProportion N s) ^ (D - r) *
          ((D - 1).choose (r - 1) : ℝ) *
          realTerminalSpendTerm theta r D) *
            ((fixedSet N s).card : ℝ) := by ring
end CollatzEndpointTransport.FixedTotal
