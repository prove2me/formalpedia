-- Prove2me | solution 1 for Formalism.L2.DIV.tauLatG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:14.904706+00:00
-- url     : https://prove2.me/submissions/06ba8083-410b-4166-8142-8679edc5546f

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Theorems.Thm_Formalism_L2_DIV_embGL_coe
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
namespace Formalism.L2.DIV
theorem _root_.solution : TauLatG := by
  intro E K _ _ _ _ ι n emb τ L γ
  unfold tauLat gLat
  rw [Submodule.map_span]
  congr 1
  ext y
  simp only [Set.mem_image, SetLike.mem_coe, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨_, ⟨x, hx, rfl⟩, ?_⟩
    funext a
    simp [embGL_coe, Matrix.mulVec, dotProduct, map_sum]
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨_, ⟨x, hx, rfl⟩, ?_⟩
    funext a
    simp [embGL_coe, Matrix.mulVec, dotProduct, map_sum]
end Formalism.L2.DIV
