-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.lev_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:49:22.477826+00:00
-- url     : https://prove2.me/submissions/1fe826a4-e43e-4c03-a024-1ec7b7f45a08

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_mat_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_vec_ext
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
theorem _root_.solution (k r' : ℕ) (g h : Mat k r') : ιLev k 1 r' g * ιLev k 1 r' h = ιLev k 1 r' (g * h) := by
  apply mat_ext
  intro u
  rw [← mulVec_mulVec]
  apply vec_ext
  · simp only [levi_action_first_coordinate]
  · simp only [lev_act_res]
    rw [mulVec_mulVec]
  · simp only [lev_act_iL]
end Formalism.FourierDecayAlt.P.B2x5
