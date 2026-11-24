-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.lev_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:14:19.327935+00:00
-- url     : https://prove2.me/submissions/ced7450b-a8d7-4cd1-bb6e-dd7d233345c4

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_vec_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lifted_vector_first
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lift_iL
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_res_lift
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_levi_action_first_coordinate
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lev_act_iL
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lev_act_res

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
theorem _root_.solution (k r' : ℕ) (g : Mat k r') (y : Fin (2 * r' + k + 1) → ℂ) :
    ιLev k 1 r' g *ᵥ liftVec k 1 r' y = liftVec k 1 r' (g *ᵥ y) := by
  apply vec_ext <;> simp [levi_action_first_coordinate, lev_act_res, lev_act_iL, res_lift, lifted_vector_first, lift_iL]
end Formalism.FourierDecayAlt.P.B2x5
