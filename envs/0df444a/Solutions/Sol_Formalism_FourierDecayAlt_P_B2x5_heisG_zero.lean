-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.heisG_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:45:38.298412+00:00
-- url     : https://prove2.me/submissions/a6635419-bce7-4df1-9731-002572307a32

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_zero_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_mat_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lift_zero
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
theorem _root_.solution (k r' : ℕ) : heisG k r' (liftVec k 1 r' 0) 0 = 1 := by
  apply mat_ext
  intro w
  rw [heis_act', lift_zero, herm_zero_right]
  simp
end Formalism.FourierDecayAlt.P.B2x5
