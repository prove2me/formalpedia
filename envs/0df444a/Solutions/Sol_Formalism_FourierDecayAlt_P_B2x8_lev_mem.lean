-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.lev_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:49:22.271567+00:00
-- url     : https://prove2.me/submissions/f485da21-202a-4072-8564-785bc06d8185

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_UH
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_mem_UH_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_eta
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_hermitian_three_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_levi_three_block

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
theorem _root_.solution (g₁ : Mat k r') (hg : g₁ ∈ GV k r') : ιLev k 1 r' g₁ ∈ GV k (1 + r') := by
  apply mem_UH_of
  intro u v
  rw [← three_block_eta u, ← three_block_eta v, levi_three_block, levi_three_block, hermitian_three_block, hermitian_three_block, herm_UH _ hg]
end Formalism.FourierDecayAlt.P.B2x8
