-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.heisenberg_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:03:14.663922+00:00
-- url     : https://prove2.me/submissions/73695c40-6971-4486-9c28-3e36a162e558

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_zero_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_heisG_zero

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
theorem _root_.solution (k r' : ℕ) : heis0 k r' (0, 0) = 1 := by
  have h : hb k r' 0 0 = 0 := by simp [hb, herm_zero_right]
  simp only [heis0, h]
  exact heisG_zero k r'
end Formalism.FourierDecayAlt.P.B2x5
