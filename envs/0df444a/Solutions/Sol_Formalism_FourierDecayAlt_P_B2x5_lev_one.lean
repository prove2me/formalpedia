-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.lev_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:20:41.577221+00:00
-- url     : https://prove2.me/submissions/b6571eff-055c-4952-a820-e2a7ccfbb6f9

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
theorem _root_.solution (k r' : ℕ) : ιLev k 1 r' (1 : Mat k r') = 1 := by
  apply mat_ext
  intro u
  rw [one_mulVec]
  apply vec_ext <;> simp [levi_action_first_coordinate, lev_act_res, lev_act_iL]
end Formalism.FourierDecayAlt.P.B2x5
