-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.central_fixed_total_aggregate_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:59:27.549196+00:00
-- url     : https://prove2.me/submissions/3db462cc-3ed8-47de-a021-21715f8611c4

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_normalizedReverseLift_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralMomentConstant_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSourceWeight_mul_fixedRenyiMoment_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
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
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N : ℕ} {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (hN : 3 < N)
    (hsizePi :
      2 * eta ≤ centralRenyiGap theta eta * ((N : ℝ) - 1))
    (hsizeDrift :
      (1 / 2 : ℝ) ≤
        (Real.log 2 / Real.log 3 - (1 / 2 + eta)) * N)
    (hinterior :
      ∀ s ∈ centralLengthSet N eta, 1 < s ∧ s < N) :
    (∑ s ∈ centralLengthSet N eta,
        fixedSourceWeight N s * fixedRenyiMoment N s theta) ≤
      centralMomentConstant theta eta * (N + 1) ^ 2 := by
  have hconst0 := (centralMomentConstant_pos
    htheta0 htheta1 heta0 heta1).le
  calc
    (∑ s ∈ centralLengthSet N eta,
        fixedSourceWeight N s * fixedRenyiMoment N s theta) ≤
      ∑ _s ∈ centralLengthSet N eta,
        centralMomentConstant theta eta * (N + 1) := by
      apply Finset.sum_le_sum
      intro s hs
      have hsData := hinterior s hs
      have hsMem :
          s ∈ Finset.Icc 1 N ∧ InCentralRenyiWindow N s eta := by
        simpa [centralLengthSet] using hs
      exact fixedSourceWeight_mul_fixedRenyiMoment_le
        htheta0 htheta1 heta0 heta1 (by omega)
        hsData.1 hsData.2 hsMem.2
        hsizePi hsizeDrift
    _ = (centralLengthSet N eta).card *
        (centralMomentConstant theta eta * (N + 1)) := by simp
    _ ≤ (N + 1 : ℝ) *
        (centralMomentConstant theta eta * (N + 1)) := by
      gcongr
      have hcard : (centralLengthSet N eta).card ≤ N + 1 := by
        have hsub : centralLengthSet N eta ⊆ Finset.range (N + 1) := by
          intro s hs
          have hsMem : s ∈ Finset.Icc 1 N := by
            have hboth :
                s ∈ Finset.Icc 1 N ∧ InCentralRenyiWindow N s eta := by
              simpa [centralLengthSet] using hs
            exact hboth.1
          exact Finset.mem_range.mpr
            (Nat.lt_succ_of_le (Finset.mem_Icc.mp hsMem).2)
        have hc := Finset.card_le_card hsub
        simpa using hc
      exact_mod_cast hcard
    _ = centralMomentConstant theta eta * (N + 1) ^ 2 := by ring
end CollatzEndpointTransport.FixedTotal
