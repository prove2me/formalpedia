-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.re_one_div_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:22.830809+00:00
-- url     : https://prove2.me/submissions/2d671543-54b5-432d-aa58-16046ad29dde

import Definitions.Def_Formalism_ZeroFreeRegion_LogDerivRegion
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ZetaLogDerivLandauBound

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
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {w : ℂ} (h : 0 ≤ w.re) : 0 ≤ (1 / w).re := by
  rw [one_div, Complex.inv_re]
  exact div_nonneg h (Complex.normSq_nonneg w)
end Formalism.ZeroFreeDirichlet
