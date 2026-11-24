-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.restriction_base_vector_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:28:49.574839+00:00
-- url     : https://prove2.me/submissions/f1c9cdeb-5ddf-4a34-995f-7014697caa5b

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_levi_position_ne_first
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_e0_eq

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
theorem _root_.solution (k r' : ℕ) : res k r' (e0 k r') = 0 := by
  funext j
  show e0 k r' (levPos k 1 r' j) = 0
  rw [e0_eq, Pi.single_eq_of_ne (levi_position_ne_first k r' j)]
end Formalism.FourierDecayAlt.P.B2x5
