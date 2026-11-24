-- Prove2me | solution 1 for Formalism.ZF.MoebiusInverseZetaBounds.norm_term_moebius_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:42:15.881153+00:00
-- url     : https://prove2.me/submissions/dcad6404-f79f-4aee-bfdd-83c8ff30912b

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
    ‖term (fun n => ((moebius n : ℤ) : ℂ)) s n‖ ≤ ‖term (1 : ℕ → ℂ) s n‖ := by
  refine LSeries.norm_term_le s ?_
  simp only [Pi.one_apply, norm_one]
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one
end Formalism.ZF.MoebiusInverseZetaBounds
