-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.levi_fixes_base_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:11:19.806805+00:00
-- url     : https://prove2.me/submissions/6b85c2c8-6aac-4146-b745-1372006f45e7

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_vec_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_restriction_base_vector_zero
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
theorem _root_.solution (k r' : ℕ) (g : Mat k r') : ιLev k 1 r' g *ᵥ e0 k r' = e0 k r' := by
  apply vec_ext <;> simp [levi_action_first_coordinate, lev_act_res, lev_act_iL, restriction_base_vector_zero]
end Formalism.FourierDecayAlt.P.B2x5
