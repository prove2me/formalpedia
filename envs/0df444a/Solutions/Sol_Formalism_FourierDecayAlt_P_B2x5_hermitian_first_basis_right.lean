-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.hermitian_first_basis_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:05:19.614156+00:00
-- url     : https://prove2.me/submissions/6bcca482-1fd7-4cff-aff6-503ea398fb7e

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_zero_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_split
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_base_vector_first_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_base_vector_last_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_restriction_base_vector_zero

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
theorem _root_.solution (k r' : ℕ) (u : Fin (2 * (1 + r') + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) u (e0 k r') = u (iL k r') := by
  rw [herm_split, base_vector_first_one, base_vector_last_zero, restriction_base_vector_zero, herm_zero_right]
  simp
end Formalism.FourierDecayAlt.P.B2x5
