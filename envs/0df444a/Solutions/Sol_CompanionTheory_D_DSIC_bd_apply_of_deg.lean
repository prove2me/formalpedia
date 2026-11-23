-- Prove2me | solution 1 for CompanionTheory.D.DSIC.bd_apply_of_deg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:52.75083+00:00
-- url     : https://prove2.me/submissions/0c2c95e9-c8e3-4754-80aa-787a6f03bd89

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
    {A : Finset (NC ε)} (hA : A.card = j) : bd ε E x A = 0 := by
  simp only [bd, bdA, LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply, lift_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases h : i ∈ A
  · simp [ann, h]
  · simp [ann, h, hx (insert i A) (by rw [Finset.card_insert_of_notMem h]; omega)]
end CompanionTheory.D.DSIC
