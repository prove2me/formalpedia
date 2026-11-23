-- Prove2me | solution 1 for CompanionTheory.D.DSIC.lift_Gop
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:26.517803+00:00
-- url     : https://prove2.me/submissions/6603f112-773b-4ac4-8c5d-2e9119971532

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CobApplyOfDeg
import Theorems.Thm_CompanionTheory_D_DSIC_lift_ann
import Theorems.Thm_CompanionTheory_D_DSIC_lift_cre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.DSIC
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight qdet qminor)
open PI.UpqRep (lowK vNormSq IsHCParam IsURepOn IsIrredOn UJset Kset IsKFin IsKTypeOf IsWtOn inG inK IsKStableOn)
variable {n : ℕ} {ε : Fin n → Bool}
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace CompanionTheory.D.DSIC
theorem _root_.solution (T : Module.End ℂ V) (c d : Fin n) : Commute (lift ε T : Module.End ℂ (Ch ε V)) (Gop ε c d) :=
  Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ =>
    ((lift_cre T i).mul_right (lift_ann T j)).smul_right _
end CompanionTheory.D.DSIC
