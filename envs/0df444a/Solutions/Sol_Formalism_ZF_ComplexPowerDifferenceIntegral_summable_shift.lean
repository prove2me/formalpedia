-- Prove2me | solution 1 for Formalism.ZF.ComplexPowerDifferenceIntegral.summable_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:20.666262+00:00
-- url     : https://prove2.me/submissions/2ce95b21-e448-43a5-b89b-361e5b0bf572

import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormCpowSubLePoint
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_DzDifferentiableOn

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
theorem _root_.solution {p : ℝ} (hp : p < -1) : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ p) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hp)
  simpa [Nat.cast_add, Nat.cast_one] using h
end Formalism.ZF.ComplexPowerDifferenceIntegral
