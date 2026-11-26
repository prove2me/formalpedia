-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_lowBarrier_of_timeSupportCritical_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:59:48.141418+00:00
-- url     : https://prove2.me/submissions/5fc93d24-9367-4b87-8a63-94d2c7246341

import Definitions.Def_FirstPassageLinearTransport_ShrinkingHighDensity
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Theorems.Thm_FirstPassageLinearTransport_timeSupportCriticalExponent_gt_half
import Theorems.Thm_FirstPassageLinearTransport_driftGap_lt_a0
import Theorems.Thm_FirstPassageLinearTransport_endpointLambda_lt_one
import Theorems.Thm_FirstPassageLinearTransport_endpointLambda_pos
import Theorems.Thm_FirstPassageLinearTransport_endpointTolerance_lt_driftGap
import Theorems.Thm_FirstPassageLinearTransport_endpointTolerance_pos
import Theorems.Thm_FirstPassageLinearTransport_firstPassageEndpointRate_pos
import Theorems.Thm_FirstPassageLinearTransport_tendsto_endpointEntropyRate


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {A : ℝ} (hA : timeSupportCriticalExponent < A) :
    ∃ lambda t : ℝ,
      0 ≤ lambda ∧ lambda < 1 ∧
      0 < t ∧ t < driftGap ∧ t < a0 ∧
      Real.log 2 / (2 * A) < adjustableEntropyRate lambda t := by
  have hAhalf : (1 / 2 : ℝ) < A :=
    timeSupportCriticalExponent_gt_half.trans hA
  have hA0 : 0 < A := by linarith
  have hthreshold : Real.log 2 / (2 * A) < firstPassageEndpointRate := by
    have hraw := mul_lt_mul_of_pos_right hA firstPassageEndpointRate_pos
    have hidentity :
        timeSupportCriticalExponent * firstPassageEndpointRate =
          Real.log 2 / 2 := by
      unfold timeSupportCriticalExponent fixedPolylogCriticalExponent
      field_simp [ne_of_gt firstPassageEndpointRate_pos]
    rw [hidentity] at hraw
    apply (div_lt_iff₀ (mul_pos (by norm_num) hA0)).2
    nlinarith
  have hEventually : ∀ᶠ n : ℕ in atTop,
      Real.log 2 / (2 * A) <
        adjustableEntropyRate (endpointLambda n) (endpointTolerance n) :=
    tendsto_endpointEntropyRate.eventually (Ioi_mem_nhds hthreshold)
  obtain ⟨n, hn⟩ := hEventually.exists
  refine ⟨endpointLambda n, endpointTolerance n,
    (endpointLambda_pos n).le, endpointLambda_lt_one n,
    endpointTolerance_pos n, endpointTolerance_lt_driftGap n,
    (endpointTolerance_lt_driftGap n).trans driftGap_lt_a0, hn⟩
end FirstPassageLinearTransport
