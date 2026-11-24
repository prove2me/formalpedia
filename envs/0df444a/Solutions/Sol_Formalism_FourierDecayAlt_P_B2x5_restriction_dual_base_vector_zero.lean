-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.restriction_dual_base_vector_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:22:51.94436+00:00
-- url     : https://prove2.me/submissions/6249084f-3d9d-437c-8f4d-0584a6d6e0bc

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lev_ne_iL
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
theorem _root_.solution (k r' : ℕ) : res k r' (es0 k r') = 0 := by
  funext j
  show es0 k r' (levPos k 1 r' j) = 0
  rw [dual_base_vector_eq_single, Pi.single_eq_of_ne (lev_ne_iL k r' j)]
end Formalism.FourierDecayAlt.P.B2x5
