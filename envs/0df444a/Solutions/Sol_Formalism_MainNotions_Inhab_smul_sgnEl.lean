-- Prove2me | solution 1 for Formalism.MainNotions.Inhab.smul_sgnEl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:40:15.894162+00:00
-- url     : https://prove2.me/submissions/6d5f79f5-c65a-45aa-a284-9069b15a8789

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataGChain
import Definitions.Def_Formalism_SharpRestriction_InertJacobiLevels_ExtraGat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Inhab
open Formalism.MainNotions.G MvPolynomial
variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
variable (P : Places p O Kf)
namespace Formalism.MainNotions.Inhab
theorem _root_.solution (L : P.Tup) : (levAll P).smul (sgnEl P) L = L := by
  funext v
  show (L v).map ((Matrix.mulVecLin ((1 : GL (Fin (P.m + 1)) (P.Qq v)) : Matrix _ _ (P.Qq v))).restrictScalars (P.W v)) = L v
  rw [Units.val_one, Matrix.mulVecLin_one]
  exact Submodule.map_id _
end Formalism.MainNotions.Inhab
