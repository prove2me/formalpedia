-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.hermitian_matrix_mul_first
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:22:56.135998+00:00
-- url     : https://prove2.me/submissions/458d3a5f-5a4f-45bd-8e88-cd807bf4c604

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_hermitian_form_first_basis

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
theorem _root_.solution (k r' : ℕ) (u : Fin (2 * (1 + r') + k + 1) → ℂ) : (Hpk k (1 + r') *ᵥ u) (i0 k r') = u (iL k r') := by
  simp [mulVec, dotProduct, hermitian_form_first_basis]
end Formalism.FourierDecayAlt.P.B2x5
