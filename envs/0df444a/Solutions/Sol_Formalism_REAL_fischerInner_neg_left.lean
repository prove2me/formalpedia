-- Prove2me | solution 1 for Formalism.REAL.fischerInner_neg_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:14:29.913301+00:00
-- url     : https://prove2.me/submissions/e0a104d5-2b6c-49a7-b631-b8c87311b2e3

import Definitions.Def_Formalism_RealPlaceAnalysis_FockPairGl
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.REAL
variable {σ : Type*}
namespace Formalism.REAL
theorem _root_.solution (f g : MvPolynomial σ ℂ) : fockF (-f) g = -fockF f g :=
  map_neg (fischerInnerLeftHom g) f
end Formalism.REAL
