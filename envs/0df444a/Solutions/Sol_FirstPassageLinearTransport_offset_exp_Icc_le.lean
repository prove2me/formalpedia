-- Prove2me | solution 1 for FirstPassageLinearTransport.offset_exp_Icc_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:49:24.377863+00:00
-- url     : https://prove2.me/submissions/2c9bd957-cd67-45bf-87b9-db0be0ca2ab3

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Order.Interval.Finset.SuccPred
import Definitions.Def_FirstPassageLinearTransport_TerminalTail
import Definitions.Def_FirstPassageLinearTransport_MovingSharpTail
import Theorems.Thm_FirstPassageLinearTransport_shifted_linear_exp_Icc_le
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_firstBadLandingEnvelope
import Theorems.Thm_FirstPassageLinearTransport_mem_generatedFirstBadSources
import Theorems.Thm_FirstPassageLinearTransport_mem_landingBad
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_firstBadLandingEnvelope
attribute [local simp] FirstPassageLinearTransport.mem_generatedFirstBadSources
attribute [local simp] FirstPassageLinearTransport.mem_landingBad
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTaggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSources
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped BigOperators Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {c₀ c : ℝ} (hc₀ : 0 < c₀) (hc₀c : c₀ ≤ c)
    {L U : ℕ} (hLU : L ≤ U) :
    ∑ q ∈ Finset.Icc L U,
        ((q - L + 1 : ℕ) : ℝ) *
          Real.exp (-(c * ((q - L : ℕ) : ℝ))) ≤
      weightedTailConstant c₀ (c₀ / 2) := by
  have hshift :
      ∑ q ∈ Finset.Icc L U,
          ((q - L + 1 : ℕ) : ℝ) *
            Real.exp (-(c * ((q - L : ℕ) : ℝ))) =
        ∑ j ∈ Finset.Icc 0 (U - L),
          ((j + 1 : ℕ) : ℝ) * Real.exp (-(c * (j : ℝ))) := by
    have hfin : Finset.range (U + 1 - L) = Finset.Icc 0 (U - L) := by
      ext j
      simp
      omega
    rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    change
      (∑ j ∈ Finset.range (U + 1 - L),
        ((j + 1 : ℕ) : ℝ) * Real.exp (-(c * (j : ℝ)))) = _
    rw [hfin]
  rw [hshift]
  have htail := shifted_linear_exp_Icc_le hc₀ hc₀c
    (L := 0) (U := U - L) (Nat.zero_le _)
  simpa using htail
end FirstPassageLinearTransport
