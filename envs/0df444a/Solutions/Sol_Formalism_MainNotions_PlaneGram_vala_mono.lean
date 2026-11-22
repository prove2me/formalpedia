-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vala_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:19:08.861624+00:00
-- url     : https://prove2.me/submissions/aae3d1b1-7726-41b4-a45d-20dba5c6d379

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut

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
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L)
variable {sg S}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {θ θ' : ℝ} (h : θ' ≤ θ) {F : MvPolynomial (L × Fin r) K} (hF : vala sg S θ F) :
    vala sg S θ' F := le_trans (WithTop.coe_le_coe.mpr h) hF
end Formalism.MainNotions.PlaneGram
