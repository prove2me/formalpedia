-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.small_scale_exp_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:45:11.076981+00:00
-- url     : https://prove2.me/submissions/304c1bab-0cdd-4755-8a29-979aeb99c781

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ChebyshevCharacterExplicitGeneral
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormIntegralComplLe
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ExpGainFromZeroFreeRegion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (c₁ s : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 20) (hs : s < 10) :
    Real.exp (c₁ * s / 2) ≤ 3 ∧ 1 ≤ 3 * Real.exp (-(c₁ / 4) * s) := by
  constructor
  · have h : c₁ * s / 2 ≤ 1 := by nlinarith
    calc Real.exp (c₁ * s / 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr h
      _ ≤ 3 := by have := Real.exp_one_lt_d9; norm_num at this; linarith
  · have h : -(1 / 8 : ℝ) ≤ -(c₁ / 4) * s := by nlinarith
    have := Real.add_one_le_exp (-(c₁ / 4) * s)
    linarith
end Formalism.ZeroFreeDirichlet
