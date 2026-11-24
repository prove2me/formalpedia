-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x6.heis_n
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:47:02.061923+00:00
-- url     : https://prove2.me/submissions/7246b594-8dea-461c-aadb-cc2526f3bcce

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_iF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_iL_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lv_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_iF_ne_iL
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lv_ne_iF
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lv_ne_iL
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lv_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_cases3
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_herm_zero_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_heis_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_heis_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_heis_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_heis_uh
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_ent
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_bvec_lv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_zero_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_iL_val
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_nset_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res

set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x6
theorem _root_.solution (x : HPar k r') : heis0 k r' x ∈ Nset k (1 + r') := by
  rw [WeylGroupFacts.nset_iff]
  refine ⟨heis_uh x, ?_⟩
  intro i j hj hi
  rw [ent (heis0 k r' x) i j]
  rcases cases3 j with rfl | rfl | ⟨j', rfl⟩
  · have : bvec (iF k r') = e0 k r' := rfl
    rw [this]
    rcases cases3 i with rfl | rfl | ⟨i', rfl⟩
    · rw [heis_F]; simp [herm_zero_left]
    · rw [heis_L]; simp [iF_ne_iL.symm]
    · have := congrFun (heis_res x (e0 k r')) i'
      simp only [res] at this
      rw [this]; simp [lv_ne_iF]
  · rw [iL_val] at hj; omega
  · rw [bvec_lv]
    rcases cases3 i with rfl | rfl | ⟨i', rfl⟩
    · rw [iF_val, lv_val] at hi; omega
    · rw [heis_L, lift_L, if_neg (lv_ne_iL j').symm]
    · have := congrFun (heis_res x (liftVec k 1 r' (bvec j'))) i'
      rw [lift_res, lift_L] at this
      simp only [res] at this
      rw [this]
      simp [bvec, Pi.single_apply, lv_inj]
end Formalism.FourierDecayAlt.P.B2x6
