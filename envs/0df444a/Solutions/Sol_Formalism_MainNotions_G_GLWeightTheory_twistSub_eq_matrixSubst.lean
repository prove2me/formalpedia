-- Prove2me | solution 1 for Formalism.MainNotions.G.GLWeightTheory.twistSub_eq_matrixSubst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:40:12.369857+00:00
-- url     : https://prove2.me/submissions/1bfa89b9-e325-4502-ae48-e07bac5b5694

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_TwistSubEqMatrixSubst

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
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory
open Formalism.MainNotions.G
variable {R B B' : Type*} [CommRing R] [CommRing B] [CommRing B'] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι)
namespace Formalism.MainNotions.G.GLWeightTheory
theorem _root_.solution (j : Fin n) :
    twistSub (R := R) LL S j = matrixSubst LL S (coefL R n) (twistMat R n j 1) (twistMat R n j (-1)) := rfl
end Formalism.MainNotions.G.GLWeightTheory
