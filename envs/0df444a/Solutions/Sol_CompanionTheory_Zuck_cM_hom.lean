-- Prove2me | solution 1 for CompanionTheory.Zuck.cM_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:56:05.29686+00:00
-- url     : https://prove2.me/submissions/cf56edaf-2527-4183-a205-15fbf9336e85

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_MultOne
import Theorems.Thm_CompanionTheory_Zuck_cM_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_CapelliEig_unitary_Hecke_group


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped Kronecker
noncomputable section
open CompanionTheory CompanionTheory.Zuck
open BranchingSupport Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
namespace CompanionTheory.Zuck
theorem _root_.solution (hM : MatHom) (b : Bool) (B : URep k r) :
    IsHom ((vr k r b).tens (vr k r (!b)), B) (one B) (mAct (cM _)) := by
  refine hM k r _ _ B _ fun g hg => ?_
  have hu : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det _).1 (PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r g hg).1
  cases b
  · exact cM_mul (A := g) (B := (g⁻¹)ᵀ) (by rw [← transpose_mul, Matrix.nonsing_inv_mul g hu, transpose_one])
  · exact cM_mul (A := (g⁻¹)ᵀ) (B := g) (by rw [transpose_transpose, Matrix.nonsing_inv_mul g hu])
end CompanionTheory.Zuck
