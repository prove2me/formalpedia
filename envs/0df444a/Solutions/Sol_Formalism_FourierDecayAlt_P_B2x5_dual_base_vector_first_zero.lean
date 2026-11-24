-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.dual_base_vector_first_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:01:18.629872+00:00
-- url     : https://prove2.me/submissions/7581c4e2-3481-46c1-ac7f-eb3e09861386

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_last_ne_first_index
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_dual_base_vector_eq_single

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
theorem _root_.solution (k r' : ℕ) : es0 k r' (i0 k r') = 0 := by
  rw [dual_base_vector_eq_single, Pi.single_eq_of_ne (last_ne_first_index k r').symm]
end Formalism.FourierDecayAlt.P.B2x5
