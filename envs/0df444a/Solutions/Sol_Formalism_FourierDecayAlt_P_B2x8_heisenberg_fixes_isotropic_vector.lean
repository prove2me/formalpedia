-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.heisenberg_fixes_isotropic_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:07:02.35183+00:00
-- url     : https://prove2.me/submissions/97c5a05c-303a-4188-96be-a2a900920b98

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_e0_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_heisenberg_three_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_herm_zero_left

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (x : HPar k r') : heis0 k r' x *ᵥ e0 k r' = e0 k r' := by
  rw [e0_eq, heisenberg_three_block, al_herm_zero_left]
  simp
end Formalism.FourierDecayAlt.P.B2x8
