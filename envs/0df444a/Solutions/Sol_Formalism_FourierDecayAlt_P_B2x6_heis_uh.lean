-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x6.heis_uh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:28:29.169354+00:00
-- url     : https://prove2.me/submissions/5558c93c-4f52-4cde-b106-b4fd91acbe78

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_herm3
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_herm_add_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_herm_add_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_herm_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_herm_smul_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_uh_of_herm
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
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_hb_add_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_add_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_add_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_smul_left
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_herm
import Theorems.Thm_Formalism_QuantumDeterminants_ggHerm_swap

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
theorem _root_.solution (x : HPar k r') : heis0 k r' x ∈ UH (Hpk k (1 + r')) := by
  apply uh_of_herm
  intro u w
  rw [herm3, herm3 u w, heis_F, heis_F, heis_L, heis_L, heis_res, heis_res]
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, star_add, star_sub, star_mul']
  rw [← ggHerm_swap (Hpk k r') (GBasic.Hpk_herm k r') x.1 (res w)]
  have h := hb_add_star x.1 x.2
  linear_combination (star (w (iL k r')) * u (iL k r')) * h
end Formalism.FourierDecayAlt.P.B2x6
