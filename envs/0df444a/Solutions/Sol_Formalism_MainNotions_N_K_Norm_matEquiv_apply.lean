-- Prove2me | solution 1 for Formalism.MainNotions.N.K.Norm.matEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:27:14.229385+00:00
-- url     : https://prove2.me/submissions/b3c8ba08-cb63-46d1-8f49-a019efb1c22c

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_AdmissibleDesigns_InvariantsEqBotIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Formalism.WeaklyAdmissibleFiltrations TensorProduct
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.MainNotions.N.K.Norm
variable {Γ : Type} [Group Γ] {K : Type} [CommRing K] {k : ℕ}
namespace Formalism.MainNotions.N.K.Norm
theorem _root_.solution (P Q : Matrix (Fin k) (Fin k) K) (h1 : P * Q = 1) (h2 : Q * P = 1) (v : Fin k → K) :
    matEquiv P Q h1 h2 v = P.mulVec v := rfl
end Formalism.MainNotions.N.K.Norm
