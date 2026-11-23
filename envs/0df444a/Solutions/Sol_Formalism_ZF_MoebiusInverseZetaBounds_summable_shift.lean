-- Prove2me | solution 1 for Formalism.ZF.MoebiusInverseZetaBounds.summable_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:21.016322+00:00
-- url     : https://prove2.me/submissions/d749f0f1-6460-45ec-9edb-dcf1c977052e

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZetaInvBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology LSeries ArithmeticFunction
noncomputable section
open Formalism Formalism.ZF
open Formalism.ZF.MoebiusInverseZetaBounds
namespace Formalism.ZF.MoebiusInverseZetaBounds
theorem _root_.solution {p : ℝ} (hp : p < -1) : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ p) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hp)
  simpa only [Nat.cast_add, Nat.cast_one] using h
end Formalism.ZF.MoebiusInverseZetaBounds
