-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.Good.smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:03:43.68024+00:00
-- url     : https://prove2.me/submissions/bc921c19-c838-4fc3-b1b7-242002cd7102

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CollapseExponent
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_Monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K)
namespace Formalism.MainNotions.PlaneGram.TwistData
namespace Good
theorem _root_.solution {p : ℕ} {Z : MvPolynomial (D.ML × Fin D.r) K} (hZ : D.Good p Z) (a : K) :
    D.Good p (a • Z) := fun ζ hζ => hZ ζ (support_smul hζ)
end Good
end Formalism.MainNotions.PlaneGram.TwistData
