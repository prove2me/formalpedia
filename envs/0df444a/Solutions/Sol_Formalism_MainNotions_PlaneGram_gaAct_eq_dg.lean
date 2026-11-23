-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.gaAct_eq_dg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:18.376551+00:00
-- url     : https://prove2.me/submissions/c8e7c747-f8be-4db8-ac90-2d9e03ce5626

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapCastMono
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
import Theorems.Thm_Formalism_MainNotions_PlaneGram_dg_eq_sum_f

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
variable {K : Type} [Field K]
variable {σ : Type}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (D : TwistData K) (G : MvPolynomial (D.OL × Fin D.r) K) :
    D.gaAct G = dg D.ga G := by
  rw [dg_eq_sum_f]; rfl
end Formalism.MainNotions.PlaneGram
