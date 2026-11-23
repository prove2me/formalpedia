-- Prove2me | solution 1 for Formalism.REAL.fischerInner_X_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:21:14.639879+00:00
-- url     : https://prove2.me/submissions/d8115632-d4d3-44d4-a29f-7989ce070bf6

import Definitions.Def_Formalism_RealPlaceAnalysis_FockPairGl
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Theorems.Thm_Formalism_REAL_fischerInner_eq_star
import Theorems.Thm_Formalism_REAL_fischerInner_pderiv_left

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
theorem _root_.solution [DecidableEq σ] (v : σ) (f g : MvPolynomial σ ℂ) :
    fockF (X v * f) g = fockF f (pderiv v g) := by
  rw [fischerInner_eq_star, ← fischerInner_pderiv_left, ← fischerInner_eq_star]
end Formalism.REAL
