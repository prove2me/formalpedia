-- Prove2me | solution 1 for Formalism.ZF.MoebiusInverseZetaBounds.norm_term_one_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:32.753904+00:00
-- url     : https://prove2.me/submissions/ac341078-1da2-4432-b7b2-7de9d91f00c4

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
theorem _root_.solution (s : ℂ) (n : ℕ) :
    ‖term (1 : ℕ → ℂ) s (n + 1)‖ = ((n : ℝ) + 1) ^ (-(s.re - 1) - 1) := by
  rw [LSeries.norm_term_eq, if_neg (Nat.succ_ne_zero n)]
  simp only [Pi.one_apply, norm_one]
  push_cast
  rw [show -(s.re - 1) - 1 = -s.re by ring, Real.rpow_neg (by positivity), one_div]
end Formalism.ZF.MoebiusInverseZetaBounds
