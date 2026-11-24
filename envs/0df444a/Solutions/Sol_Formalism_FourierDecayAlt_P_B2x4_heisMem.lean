-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x4.heisMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:09:36.919096+00:00
-- url     : https://prove2.me/submissions/b7c6f002-6e20-44ef-8063-2c45942654ab

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_mem_UH_of_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_heis_isom
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_Hpk_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_hermitian_first_basis_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_hermitian_form_base_vector_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_goodRowsProjector_apply_eq_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_liftVec_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_herm_lift
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_hb_rel
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_heisAct
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_heisG_apply
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_herm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x4
theorem _root_.solution : HeisMem := by
  intro k r' x
  obtain ⟨y, s⟩ := x
  refine ⟨?_, ?_, ?_⟩
  · apply mem_UH_of_herm
    intro u w
    simp only [heis0]
    rw [heisAct, heisAct]
    apply heis_isom _ (Hpk_herm k (1 + r'))
    · rw [hermitian_first_basis_right, goodRowsProjector_apply_eq_sum]; simp [lastI]
    · rw [hermitian_first_basis_right, liftVec_last]
    · rw [herm_lift]; exact hb_rel k r' y s
  · intro a i hai
    have ha := a.isLt
    simp only [heis0]
    have hv : (eI k (1 + r') a).val = a.val := rfl
    have hz : (if (eI k (1 + r') a).val = 2 * (1 + r') + k then (1 : ℂ) else 0) = 0 := if_neg (by omega)
    rw [heisG_apply, hz, mul_zero, add_zero, goodRowsProjector_apply_eq_sum]
    by_cases hi : i.val = 0
    · have : bvec (eI k (1 + r') a) = e0 k r' := by
        unfold e0; congr 1; apply Fin.ext; simp only [eI, a0]; omega
      rw [this, hermitian_form_base_vector_left, liftVec_last]; simp
    · rw [if_neg hi]; simp
  · intro i j h1 h2 h3
    simp only [heis0]
    have hz : (if j.val = 2 * (1 + r') + k then (1 : ℂ) else 0) = 0 := if_neg (by omega)
    have hz2 : (if i.val = 0 then (1 : ℂ) else 0) = 0 := if_neg (by omega)
    rw [heisG_apply, hz, mul_zero, add_zero, goodRowsProjector_apply_eq_sum, hz2]; simp
end Formalism.FourierDecayAlt.P.B2x4
