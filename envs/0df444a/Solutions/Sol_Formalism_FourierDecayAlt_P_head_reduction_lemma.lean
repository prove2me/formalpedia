-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.head_reduction_lemma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:18:49.310826+00:00
-- url     : https://prove2.me/submissions/0e8ae62e-df3c-4211-8fe6-4368eda6a6c7

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_two_block_point_block_matrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_add_blk
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_PhiH_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_PhiH_supp
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_top_main
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_sum_identity
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_mem_mulR
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_PhiH_const
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_fib
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_gl_coe
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_left_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_m_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_mem_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_right_eq
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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism.FourierDecayAlt.P.A5x8 (sec_m sec_m_ext sec_gl sec_gl_coe sec_fib sec_right_eq sec_left_eq sec_mem_int toCos)
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open TwoBlockPoint
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.HeadReduction := by
  intro K _ _ _ R ψ hD hn m h Q hQc hQu
  obtain ⟨ϖ, hϖR, hϖK, hu, hbd⟩ := top_main R ψ hD hn
  obtain ⟨k, hk⟩ := hbd Q hQc hQu
  obtain ⟨j, hj⟩ := hϖK ((pt h.1 h.2).det ^ 2)
  have hψ : ∀ r ∈ R, ψ r = 1 := fun r hr => by simpa using (hD.selfDual 1).2 R.one_mem r hr
  have hdpt := pt_unit_lemma_5 h.1 h.2
  have hu0inv : ((hdpt.unit⁻¹ : Kˣ) : K) = Ring.inverse (pt h.1 h.2).det := by
    rw [← Ring.inverse_unit, IsUnit.unit_spec]
  have hlat : ∀ u : Kˣ, IsLat (mulR R (u : K)) := by
    intro u
    have e : ((mulR R (u : K)) : Set K) = (fun x => ((u⁻¹ : Kˣ) : K) * x) ⁻¹' (R : Set K) := by
      unfold mulR
      rw [AddSubgroup.coe_map, AddMonoidHom.coe_mulLeft]
      refine congrFun (Set.image_eq_preimage_of_inverse (fun x => ?_) (fun x => ?_)) _
      · show ((u⁻¹ : Kˣ) : K) * ((u : K) * x) = x
        rw [← mul_assoc, Units.inv_mul, one_mul]
      · show (u : K) * (((u⁻¹ : Kˣ) : K) * x) = x
        rw [← mul_assoc, Units.mul_inv, one_mul]
    refine ⟨?_, ?_⟩
    · rw [e]
      exact hD.isOpen.preimage (continuous_mul_left _)
    · unfold mulR
      rw [AddSubgroup.coe_map, AddMonoidHom.coe_mulLeft]
      exact hD.isCompact.image (continuous_mul_left _)
  refine ⟨mulR R ((hdpt.unit⁻¹ : Kˣ) : K), mulR R ((hdpt.unit ^ 2 * ϖ ^ (2 * k + 1 + j) : Kˣ) : K),
    hlat _, hlat _, fun n' Z' => ⟨fun n => PhiH R ψ h Z' n, ?_,
      fun t c => sum_identity R (two_block_point_size_sum h m t c) (two_block_point_block_matrix h m t c) ψ hD Z',
      fun z => sum_identity R (add_sum h (m + 1) z) (add_blk h (m + 1) z) ψ hD Z'⟩⟩
  unfold PhiHyp
  refine ⟨fun Z a b ha hai hb hbi => PhiH_inv R ψ hψ h Z' (m + 1) Z a b ha hai hb hbi,
    fun Z hne i l => ?_, fun Z Y hZ hY => ?_⟩
  · obtain ⟨r, hr, e⟩ := PhiH_supp R ψ h Z' (m + 1) Z hne i l
    refine (mem_mulR R).2 ⟨r, hr, ?_⟩
    rw [e, hu0inv]
  · have hE : ∀ i l, ∃ r ∈ R, Y i l = (pt h.1 h.2).det ^ 2 * (ϖ : K) ^ (2 * k + 1 + j) * r := by
      intro i l
      obtain ⟨r, hr, e⟩ := (mem_mulR R).1 (hY i l)
      refine ⟨r, hr, ?_⟩
      rw [e, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
    rcases hZ with hZ | hZ
    · exact PhiH_const R ψ h Z' (ϖ : K) hϖR hu k j hj (m + 1) Z Y (Ring.inverse Z.det)
        (Ring.mul_inverse_cancel _ (hQu _ hZ)) (hk _ hZ) hE
    · refine PhiH_const R ψ h Z' (ϖ : K) hϖR hu k j hj (m + 1) Z Y (-Ring.inverse (-Z.det)) ?_ ?_ hE
      · rw [mul_neg, ← neg_mul, Ring.mul_inverse_cancel _ (hQu _ hZ)]
      · rw [mul_neg]
        exact R.neg_mem (hk _ hZ)
end Formalism.FourierDecayAlt.P
