-- Prove2me | solution 1 for Formalism.landauIteratedDerivatives.dist_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:46:33.38515+00:00
-- url     : https://prove2.me/submissions/4d295437-3a75-4d7d-848c-e4e8386db2ef

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_LandauLemma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
open Formalism.landauIteratedDerivatives
namespace Formalism.landauIteratedDerivatives
theorem _root_.solution (z : ℂ) : dist z (z.re : ℂ) = |z.im| := by
  rw [Complex.dist_eq_re_im, Complex.ofReal_re, Complex.ofReal_im, sub_self, sub_zero,
    show (0 : ℝ) ^ 2 + z.im ^ 2 = z.im ^ 2 by ring, Real.sqrt_sq_eq_abs]
end Formalism.landauIteratedDerivatives
