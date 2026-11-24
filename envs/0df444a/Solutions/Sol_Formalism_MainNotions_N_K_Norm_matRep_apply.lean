-- Prove2me | solution 1 for Formalism.MainNotions.N.K.Norm.matRep_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:28:21.187816+00:00
-- url     : https://prove2.me/submissions/1155a45a-82e5-4e35-b0f4-b4e5d572a773

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_AdmissibleDesigns_InvariantsEqBotIff
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Module Formalism.WeaklyAdmissibleFiltrations TensorProduct
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.MainNotions.N.K.Norm
variable {Γ : Type} [Group Γ] {K : Type} [CommRing K] {k : ℕ}
namespace Formalism.MainNotions.N.K.Norm
theorem _root_.solution (M : Γ →* Matrix (Fin k) (Fin k) K) (g : Γ) (v : Fin k → K) :
    matRep M g v = (M g).mulVec v := by
  simp [matRep, Matrix.toLinAlgEquiv'_apply]
end Formalism.MainNotions.N.K.Norm
