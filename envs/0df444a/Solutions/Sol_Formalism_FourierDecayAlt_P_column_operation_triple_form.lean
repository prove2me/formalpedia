-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.column_operation_triple_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:39:19.055005+00:00
-- url     : https://prove2.me/submissions/71245ed9-3ea6-4767-b866-1836494b3780

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_colOp_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_lamTil_fin
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_lamN_latZ
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_lamLin_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_liftRel_symm
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_A5x2_liftRel_symm__82d048f68e41
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_inTTeq_symm
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_exists_lift
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_lin_lift
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_lift_lat
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_uniq_lat
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_lamTil_colOp
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x2 Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A5.ColOpTriple := by
  intro K _ R n Z Z' hZ hZ' hd hd' φ hφ c hT he m m' hm hm0
  have hm0' : ∀ j, c.val ≤ j → lamTil R Z' j m' = 0 := fun j hj => by rw [hm.2 j hj, hm0 j hj]
  have hc : (Z⁻¹ *ᵥ coeLin R m) c = 0 := by rw [← lamTil_fin]; exact hm0 _ le_rfl
  have hc' : (Z'⁻¹ *ᵥ coeLin R m') c = 0 := by rw [← lamTil_fin]; exact hm0' _ le_rfl
  have hd1' := colOp_det Z' (coeLin R m') c hd' hc'
  obtain ⟨F, hF⟩ := lin_lift R Z Z' φ c.val (exists_lift R Z Z' hZ' hd' φ c.val hT)
  obtain ⟨G, hG⟩ := lin_lift R Z' Z φ.symm c.val
    (exists_lift R Z' Z hZ hd φ.symm c.val (inTTeq_symm hT))
  have hms := liftRel_symm hm
  let φn : coker R (Z + vecMulVec (coeLin R m) (Pi.single c 1)) ≃ₗ[R]
      coker R (Z' + vecMulVec (coeLin R m') (Pi.single c 1)) :=
    LinearEquiv.ofLinearMap
      (Submodule.mapQ _ _ F (fun v hv => lift_lat R Z Z' hd hd' φ c m m' v (F v) hm (hF v) hv))
      (Submodule.mapQ _ _ G
        (fun v hv => lift_lat R Z' Z hd' hd φ.symm c m' m v (G v) hms (hG v) hv))
      (by
        apply LinearMap.ext
        intro x
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        show Submodule.Quotient.mk (F (G v)) = Submodule.Quotient.mk v
        rw [Submodule.Quotient.eq]
        exact uniq_lat R Z Z' hd hd' φ c m m' (G v) _ _ hm (hF _) (liftRel_symm' (hG v)))
      (by
        apply LinearMap.ext
        intro x
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        show Submodule.Quotient.mk (G (F v)) = Submodule.Quotient.mk v
        rw [Submodule.Quotient.eq]
        exact uniq_lat R Z' Z hd' hd φ.symm c m' m (F v) _ _ hms (hG _) (liftRel_symm (hF v)))
  have hφn : ∀ v v', LiftRel R c.val Z Z' φ v v' →
      φn (Submodule.Quotient.mk v) = Submodule.Quotient.mk v' := by
    intro v v' h
    show Submodule.Quotient.mk (F v) = Submodule.Quotient.mk v'
    rw [Submodule.Quotient.eq]
    exact uniq_lat R Z Z' hd hd' φ c m m' v _ _ hm (hF v) h
  have hlam : ∀ j, c.val ≤ j → ∀ v v', φn (Submodule.Quotient.mk v) = Submodule.Quotient.mk v' →
      lamN R (Z' + vecMulVec (coeLin R m') (Pi.single c 1)) j v' =
        lamN R (Z + vecMulVec (coeLin R m) (Pi.single c 1)) j v := by
    intro j hj v v' h
    have h1 : (Submodule.Quotient.mk (F v) :
        coker R (Z' + vecMulVec (coeLin R m') (Pi.single c 1))) = Submodule.Quotient.mk v' := h
    rw [Submodule.Quotient.eq] at h1
    have h2 := lamN_latZ R _ hd1' j h1
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h2
    rw [← h2]
    simp only [lamN, LinearMap.comp_apply]
    rw [lamTil_colOp R Z hd m c hm0 j hj, lamTil_colOp R Z' hd' m' c hm0' j hj, (hF v).2 j hj]
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) c.2
  refine ⟨φn, ⟨hφn _ _ he, fun v v' h => ?_⟩, fun j hj _ v v' h => hlam j hj v v' h, hφn⟩
  rw [lamLin_eq R _ hn, lamLin_eq R _ hn]
  exact hlam (n - 1) (by have := c.2; omega) v v' h
end Formalism.FourierDecayAlt.P
