-- Prove2me | solution 1 for CompanionTheory.D.DSIC.cob_apply_of_deg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:52.845399+00:00
-- url     : https://prove2.me/submissions/0962829e-9a21-4753-9f85-68dd7474070d

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CobApplyOfDeg
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



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
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ V) {j : ℕ} {x : Ch ε V} (hx : Deg j x)
    {A : Finset (NC ε)} (hA : A.card = j) : cob ε E x A = 0 := by
  simp only [cob, LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply, lift_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases h : i ∈ A
  · have := Finset.card_erase_add_one h
    simp [cre, h, hx (A.erase i) (by omega)]
  · simp [cre, h]
end CompanionTheory.D.DSIC
