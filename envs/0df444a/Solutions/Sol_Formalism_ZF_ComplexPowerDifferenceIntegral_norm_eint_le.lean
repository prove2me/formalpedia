-- Prove2me | solution 1 for Formalism.ZF.ComplexPowerDifferenceIntegral.norm_eint_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:29:52.562272+00:00
-- url     : https://prove2.me/submissions/c5a69eec-6929-4595-96ea-8f955447d0bf

import Mathlib
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormCpowSubLePoint
import Theorems.Thm_Formalism_ZF_ComplexPowerDifferenceIntegral_norm_cpow_sub_le_point

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.ZF
open Formalism.ZF.ComplexPowerDifferenceIntegral
namespace Formalism.ZF.ComplexPowerDifferenceIntegral
theorem _root_.solution {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    ‖eint s a‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by
  unfold eint
  have hC : ∀ x ∈ Set.uIoc a (a + 1),
      ‖((x : ℂ) ^ (-s) - ((a + 1 : ℝ) : ℂ) ^ (-s))‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    exact norm_cpow_sub_le_point ha hx.1.le hx.2 hs
  calc _ ≤ ‖s‖ * a ^ (-s.re - 1) * |a + 1 - a| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hC
    _ = _ := by rw [show a + 1 - a = 1 by ring, abs_one, mul_one]
end Formalism.ZF.ComplexPowerDifferenceIntegral
