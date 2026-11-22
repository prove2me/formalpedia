-- Prove2me | solution 1 for Formalism.REAL.fischerInner_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:15:18.190304+00:00
-- url     : https://prove2.me/submissions/5e9b230c-12d2-48da-9338-3fa206c9a040

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
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : MvPolynomial σ ℂ) (h : ι → MvPolynomial σ ℂ) :
    fockF f (∑ a ∈ s, h a) = ∑ a ∈ s, fockF f (h a) :=
  map_sum (fischerInnerRightHom f) h s
end Formalism.REAL
