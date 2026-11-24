-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.al_cF_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:49:11.868819+00:00
-- url     : https://prove2.me/submissions/d41653fe-1ea4-4cc8-b204-ae8f11da0208

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_eta
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_dual_base_vector_eq_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_hermitian_three_block

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
theorem _root_.solution (u : Fin (2 * (1 + r') + k + 1) → ℂ) : herm (Hpk k (1 + r')) u (es0 k r') = cF u := by
  have h := hermitian_three_block (k := k) (r' := r') (cF u) 0 (cL u) 1 (mid u) 0
  rw [three_block_eta, ← dual_base_vector_eq_single] at h
  rw [h]
  simp [herm]
end Formalism.FourierDecayAlt.P.B2x8
