-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.al_oneStep_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:28:23.788992+00:00
-- url     : https://prove2.me/submissions/4fad6df4-ced2-4acd-b496-16bb8c5cbd8d

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_mul_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_inv_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_heis_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_cmHalfIntegralGenerator_mem_algebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_lev_mem

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
theorem _root_.solution (x x' : HPar k r') {c : ℂ} (hc : c ≠ 0) {g₁ : Mat k r'} (hg : g₁ ∈ GV k r') :
    oneStep k r' x c g₁ x' ∈ GV k (1 + r') := by
  unfold oneStep
  exact al_mul_mem (al_mul_mem (al_mul_mem (al_inv_mem (heis_mem x)) (cmHalfIntegralGenerator_mem_algebraicClosure c hc)) (lev_mem g₁ hg)) (heis_mem x')
end Formalism.FourierDecayAlt.P.B2x8
