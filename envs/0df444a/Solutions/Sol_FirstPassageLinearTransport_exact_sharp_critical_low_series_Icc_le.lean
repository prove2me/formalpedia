-- Prove2me | solution 1 for FirstPassageLinearTransport.exact_sharp_critical_low_series_Icc_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:01:10.657048+00:00
-- url     : https://prove2.me/submissions/466112bb-634e-4c5e-a466-94e2f2d2c47c

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Order.Interval.Finset.SuccPred
import Definitions.Def_FirstPassageLinearTransport_TerminalTail
import Definitions.Def_FirstPassageLinearTransport_MovingSharpTail
import Theorems.Thm_FirstPassageLinearTransport_shifted_linear_exp_Icc_le
import Theorems.Thm_FirstPassageLinearTransport_sharp_entropy_tail_exact_rate_Icc_le
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
    {b₀ b Cpref : ℝ} (hb₀ : 0 < b₀) (hb₀b : b₀ ≤ b)
    (hCpref : 0 ≤ Cpref) {L U : ℕ} (hL : 2 ≤ L) (hLU : L ≤ U) :
    ∑ q ∈ Finset.Icc L U,
        ((q + 1 : ℕ) : ℝ) *
          (Real.exp (-(Real.log 2 * (q : ℝ))) +
            Cpref / Real.sqrt ((q - 1 : ℕ) : ℝ) *
              Real.exp (-(b * ((q - 1 : ℕ) : ℝ)))) ≤
      weightedTailConstant (Real.log 2) (Real.log 2 / 2) *
          ((L + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (L : ℝ))) +
        3 * Cpref * weightedTailConstant b₀ (b₀ / 2) *
          Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ))) := by
  have hsplit :
      ∑ q ∈ Finset.Icc L U,
          ((q + 1 : ℕ) : ℝ) *
            (Real.exp (-(Real.log 2 * (q : ℝ))) +
              Cpref / Real.sqrt ((q - 1 : ℕ) : ℝ) *
                Real.exp (-(b * ((q - 1 : ℕ) : ℝ)))) =
        ∑ q ∈ Finset.Icc L U,
            ((q + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (q : ℝ))) +
          Cpref * ∑ q ∈ Finset.Icc L U,
            ((q + 1 : ℕ) : ℝ) / Real.sqrt ((q - 1 : ℕ) : ℝ) *
              Real.exp (-(b * ((q - 1 : ℕ) : ℝ))) := by
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  rw [hsplit]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdy := shifted_linear_exp_Icc_le hlog2 le_rfl hLU
  have hent := sharp_entropy_tail_exact_rate_Icc_le hb₀ hb₀b hL hLU
  calc
    ∑ q ∈ Finset.Icc L U,
          ((q + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (q : ℝ))) +
        Cpref * ∑ q ∈ Finset.Icc L U,
          ((q + 1 : ℕ) : ℝ) / Real.sqrt ((q - 1 : ℕ) : ℝ) *
            Real.exp (-(b * ((q - 1 : ℕ) : ℝ))) ≤
      (((L + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (L : ℝ))) *
          weightedTailConstant (Real.log 2) (Real.log 2 / 2)) +
        Cpref * (3 * Real.sqrt L *
          Real.exp (-(b * ((L - 1 : ℕ) : ℝ))) *
            weightedTailConstant b₀ (b₀ / 2)) := by
        exact add_le_add hdy (mul_le_mul_of_nonneg_left hent hCpref)
    _ = weightedTailConstant (Real.log 2) (Real.log 2 / 2) *
          ((L + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (L : ℝ))) +
        3 * Cpref * weightedTailConstant b₀ (b₀ / 2) *
          Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ))) := by ring
end FirstPassageLinearTransport
