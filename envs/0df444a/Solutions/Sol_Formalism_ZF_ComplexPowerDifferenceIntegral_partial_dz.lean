-- Prove2me | solution 1 for Formalism.ZF.ComplexPowerDifferenceIntegral.partial_dz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:42:14.773079+00:00
-- url     : https://prove2.me/submissions/b934adc1-6367-48da-a476-3d9532391bc5

import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_DzDifferentiableOn
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RiemannZetaOneEqOneSubOfRePos

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
theorem _root_.solution (s : ℂ) (N : ℕ) :
    ∑ i ∈ Finset.range N, dz s i =
      1 - (((N : ℝ) + 1 : ℝ) : ℂ) ^ (1 - s) -
        (s - 1) * ∑ i ∈ Finset.range N, ((((i : ℝ) + 1) + 1 : ℝ) : ℂ) ^ (-s) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp only [dz]
    push_cast
    ring
end Formalism.ZF.ComplexPowerDifferenceIntegral
