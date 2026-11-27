-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.ValuationFitting.vA_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:35:11.862386+00:00
-- url     : https://prove2.me/submissions/32a0e8aa-777d-4911-b763-a5fc05390a92

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_DualLattices_U10
import Definitions.Def_ReciprocityTheory_DualLattices_KilledGen
import Definitions.Def_ReciprocityTheory_DualLattices_IdemGen
import Definitions.Def_ReciprocityTheory_DualLattices_LenEx
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_FittingIdeal_DetMulMemFitt0
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PlugUP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
open Formalism.L2.FormalSeriesBounds.ValuationFitting
open ReciprocityTheory.PGsh.Up CharacteristicFromRanks
variable {C : Type} [Field C]
variable {V : VF C} {vm : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
namespace Formalism.L2.FormalSeriesBounds.ValuationFitting
theorem _root_.solution (x : R) : vA V R x = V.v (algebraMap R C x) := rfl
end Formalism.L2.FormalSeriesBounds.ValuationFitting
