-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.heisG_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:45:37.369867+00:00
-- url     : https://prove2.me/submissions/8d9fcc5f-6a26-424a-9c1a-b19c6f45c658

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_add_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_add_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_mat_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_base_vector_last_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_restriction_base_vector_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lift_iL
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_res_lift
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_res_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_res_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_res_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lift_add
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B2x5_heis_act__04df4e81c20a

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x5
theorem _root_.solution (k r' : ℕ) (y y' : Fin (2 * r' + k + 1) → ℂ) (b b' : ℂ) :
    heisG k r' (liftVec k 1 r' y) b * heisG k r' (liftVec k 1 r' y') b' =
      heisG k r' (liftVec k 1 r' (y + y')) (b + b' - herm (Hpk k r') y' y) := by
  apply mat_ext
  intro w
  rw [← mulVec_mulVec, heis_act', heis_act', heis_act']
  have hL : (w - herm (Hpk k r') (res k r' w) y' • e0 k r' + w (iL k r') • (liftVec k 1 r' y' + b' • e0 k r'))
      (iL k r') = w (iL k r') := by
    simp [base_vector_last_zero, lift_iL]
  have hR : res k r' (w - herm (Hpk k r') (res k r' w) y' • e0 k r' +
      w (iL k r') • (liftVec k 1 r' y' + b' • e0 k r')) = res k r' w + w (iL k r') • y' := by
    simp only [res_add, res_sub, res_smul, restriction_base_vector_zero, res_lift, smul_zero, sub_zero, add_zero]
  rw [hL, hR, herm_add_left, herm_smul_left, herm_add_right, lift_add]
  funext p
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring
end Formalism.FourierDecayAlt.P.B2x5
