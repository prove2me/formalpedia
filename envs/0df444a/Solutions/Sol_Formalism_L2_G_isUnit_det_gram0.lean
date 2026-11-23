-- Prove2me | solution 1 for Formalism.L2.G.isUnit_det_gram0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:21.170848+00:00
-- url     : https://prove2.me/submissions/3d8646ce-a9e9-4b98-b0cd-ab162ee60f9b

import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_LevelGatherings_GramDetIsUnit
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions NumberField Formalism.UG
open Formalism Formalism.L2 Formalism.L2.G
variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
namespace Formalism.L2.G
theorem _root_.solution (sp : Spaces R F E) : IsUnit sp.gram0.det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  rw [Spaces.gram0, Matrix.det_reindex_self] at hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hi : ∀ i, (sp.X 0).hT ((sp.X 0).frame i) (∑ j, v j • (sp.X 0).frame j) = 0 := by
    intro i
    have h := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, HSpace.gram, Pi.zero_apply] at h
    simp only [map_sum, map_smul, smul_eq_mul]
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hy : ∀ x, (sp.X 0).hT x (∑ j, v j • (sp.X 0).frame j) = 0 := by
    intro x
    rw [← (sp.X 0).frame.sum_repr x, map_sum (sp.X 0).hT, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hi, smul_zero]
  have h0 := (sp.X 0).nondeg.2 _ hy
  have hv' := Fintype.linearIndependent_iff.mp (sp.X 0).frame.linearIndependent v h0
  exact hv0 (funext hv')
end Formalism.L2.G
