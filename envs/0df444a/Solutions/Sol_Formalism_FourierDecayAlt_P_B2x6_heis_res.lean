-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x6.heis_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:11:33.892859+00:00
-- url     : https://prove2.me/submissions/7862e03d-45af-4162-b3b6-ff0e4600fd7a

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_res_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_res_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_res_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_hermitian_form_base_vector_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_herm_lift
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_heisAct
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_res_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_res_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_res_sub

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
theorem _root_.solution (x : HPar k r') (u : Fin (2 * (1 + r') + k + 1) → ℂ) :
    res (heis0 k r' x *ᵥ u) = res u + u (iL k r') • x.1 := by
  rw [heis0, heisAct, hermitian_form_base_vector_right, herm_lift]
  simp [res_add, res_sub, res_smul]
end Formalism.FourierDecayAlt.P.B2x6
