-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.heisenberg_dual_base_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:06:58.999801+00:00
-- url     : https://prove2.me/submissions/4baa3f45-825c-455b-a563-87d26b62447a

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_dual_base_vector_eq_single
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
theorem _root_.solution (x : HPar k r') : heis0 k r' x *ᵥ es0 k r' = mk3 k r' (hb k r' x.1 x.2) x.1 1 := by
  rw [dual_base_vector_eq_single, heisenberg_three_block, al_herm_zero_left]
  simp
end Formalism.FourierDecayAlt.P.B2x8
