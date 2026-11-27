-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.ValuationFitting.lenCoker_vA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:40:38.276503+00:00
-- url     : https://prove2.me/submissions/020ecc13-21b8-402e-97ed-7b3b4e41dad2

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_DualLattices_U10
import Definitions.Def_ReciprocityTheory_DualLattices_KilledGen
import Definitions.Def_ReciprocityTheory_DualLattices_IdemGen
import Definitions.Def_ReciprocityTheory_DualLattices_LenEx
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_FittingIdeal_DetMulMemFitt0
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PlugUP
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationFitting_vA_apply

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
theorem _root_.solution {m h : ℕ} (α : Matrix (Fin m) (Fin h) R) :
    S4.lenCoker (vA V R) α = S4.lenCoker V.v (Matrix.of fun i k => algebraMap R C (α i k)) := by
  unfold S4.lenCoker
  congr 1
  funext g
  rw [vA_apply, RingHom.map_det]
  rfl
end Formalism.L2.FormalSeriesBounds.ValuationFitting
