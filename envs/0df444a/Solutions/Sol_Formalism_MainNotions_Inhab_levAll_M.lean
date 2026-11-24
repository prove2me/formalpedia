-- Prove2me | solution 1 for Formalism.MainNotions.Inhab.levAll_M
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:49:03.656848+00:00
-- url     : https://prove2.me/submissions/384be66b-607e-41ee-a082-02a1ff17662d

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataGChain
import Definitions.Def_Formalism_SharpRestriction_InertJacobiLevels_ExtraGat
import Theorems.Thm_Formalism_MainNotions_Inhab_levAll_funMod

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
theorem _root_.solution (h2 : (2 : Kf) ≠ 0) : (levAll P).M = ⊥ := levAll_funMod P h2 _
end Formalism.MainNotions.Inhab
