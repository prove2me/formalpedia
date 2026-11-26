-- Prove2me | solution 1 for FirstPassageLinearTransport.terminal_rank_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:48:08.292823+00:00
-- url     : https://prove2.me/submissions/90be98d6-21e2-4a9a-b499-6dceba2ca1f5

import Definitions.Def_FirstPassageLinearTransport_TerminalTail
import Definitions.Def_FirstPassageLinearTransport_TerminalProfile
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
import Theorems.Thm_FirstPassageLinearTransport_weighted_exp_Icc_le
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
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {b b' c' : ℝ}
    (hb' : 0 < b') (hbb' : b' < b)
    (hc' : 0 < c') (hc2 : c' < Real.log 2)
    (L U : ℕ) :
    ∑ q ∈ Finset.Icc L U,
        ((q + 1 : ℕ) : ℝ) *
          (Real.exp (-(Real.log 2 * (q : ℝ))) +
            Real.exp b * Real.exp (-(b * (q : ℝ)))) ≤
      weightedTailConstant (Real.log 2) c' *
          Real.exp (-(c' * (L : ℝ))) +
        Real.exp b * weightedTailConstant b b' *
          Real.exp (-(b' * (L : ℝ))) := by
  have hdyadic := weighted_exp_Icc_le hc' hc2 L U
  have hentropy := weighted_exp_Icc_le hb' hbb' L U
  calc
    ∑ q ∈ Finset.Icc L U,
        ((q + 1 : ℕ) : ℝ) *
          (Real.exp (-(Real.log 2 * (q : ℝ))) +
            Real.exp b * Real.exp (-(b * (q : ℝ)))) =
        (∑ q ∈ Finset.Icc L U,
          ((q + 1 : ℕ) : ℝ) *
            Real.exp (-(Real.log 2 * (q : ℝ)))) +
        Real.exp b *
          (∑ q ∈ Finset.Icc L U,
            ((q + 1 : ℕ) : ℝ) *
              Real.exp (-(b * (q : ℝ)))) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      congr 1
      calc
        ∑ q ∈ Finset.Icc L U,
            ((q + 1 : ℕ) : ℝ) *
              (Real.exp b * Real.exp (-(b * (q : ℝ)))) =
            ∑ q ∈ Finset.Icc L U,
              Real.exp b * (((q + 1 : ℕ) : ℝ) *
                Real.exp (-(b * (q : ℝ)))) := by
          apply Finset.sum_congr rfl
          intro q hq
          ring
        _ = Real.exp b *
            (∑ q ∈ Finset.Icc L U,
              ((q + 1 : ℕ) : ℝ) *
                Real.exp (-(b * (q : ℝ)))) :=
          (Finset.mul_sum (Finset.Icc L U)
            (fun q => ((q + 1 : ℕ) : ℝ) *
              Real.exp (-(b * (q : ℝ)))) (Real.exp b)).symm
    _ ≤ weightedTailConstant (Real.log 2) c' *
          Real.exp (-(c' * (L : ℝ))) +
        Real.exp b * weightedTailConstant b b' *
          Real.exp (-(b' * (L : ℝ))) := by
      have hscaled :=
        mul_le_mul_of_nonneg_left hentropy (Real.exp_pos b).le
      exact add_le_add hdyadic (by simpa [mul_assoc] using hscaled)
end FirstPassageLinearTransport
