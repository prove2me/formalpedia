-- Prove2me | solution 1 for Formalism.REAL.fischerInner_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:15:12.830934+00:00
-- url     : https://prove2.me/submissions/39158f64-e9dc-4187-a189-7444f9a75d54

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
theorem _root_.solution {ι : Type*} (s : Finset ι) (h : ι → MvPolynomial σ ℂ) (g : MvPolynomial σ ℂ) :
    fockF (∑ a ∈ s, h a) g = ∑ a ∈ s, fockF (h a) g :=
  map_sum (fischerInnerLeftHom g) h s
end Formalism.REAL
