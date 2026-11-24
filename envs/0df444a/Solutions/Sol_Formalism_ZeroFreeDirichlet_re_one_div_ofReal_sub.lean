-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.re_one_div_ofReal_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:45:08.448575+00:00
-- url     : https://prove2.me/submissions/6622fa70-e309-4c80-a440-e83df6928d8b

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_RealSmallTOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (σ : ℝ) (ρ : ℂ) :
    (1 / ((σ : ℂ) - ρ)).re = (σ - ρ.re) / ((σ - ρ.re) ^ 2 + ρ.im ^ 2) := by
  rw [one_div, Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  ring
end Formalism.ZeroFreeDirichlet
