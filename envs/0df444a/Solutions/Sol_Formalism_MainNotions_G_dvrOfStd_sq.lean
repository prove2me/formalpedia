-- Prove2me | solution 1 for Formalism.MainNotions.G.dvrOfStd_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:29:24.315558+00:00
-- url     : https://prove2.me/submissions/e30724dd-8d61-4b42-a85b-b3e7c7c14fe5

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjBridge

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
open Formalism Formalism.MainNotions Formalism.MainNotions.G
namespace Formalism.MainNotions.G
theorem _root_.solution {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (h : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w) :
    (dvrOfStd h).SqP := h.1.w_sq
end Formalism.MainNotions.G
