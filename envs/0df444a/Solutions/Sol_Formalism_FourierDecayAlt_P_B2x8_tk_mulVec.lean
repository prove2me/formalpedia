-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.tk_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:46:40.645359+00:00
-- url     : https://prove2.me/submissions/d99d866c-cac9-40ca-8454-661706159357

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_first
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_middle
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_tk_sum

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
theorem _root_.solution (A : Mat k (1 + r')) (a b : ℂ) (y : Fin (2 * r' + k + 1) → ℂ) (i : Fin (2 * (1 + r') + k + 1)) :
    (A *ᵥ mk3 k r' a y b) i = A i (tkF k r') * a + ∑ j, A i (levPos k 1 r' j) * y j + A i (tkL k r') * b := by
  simp only [Matrix.mulVec, dotProduct]
  rw [tk_sum]
  have h1 : mk3 k r' a y b (tkF k r') = a := three_block_first a y b
  have h2 : ∀ j, mk3 k r' a y b (levPos k 1 r' j) = y j := fun j => congrFun (three_block_middle a y b) j
  have h3 : mk3 k r' a y b (tkL k r') = b := three_block_last a y b
  simp only [h1, h2, h3]
end Formalism.FourierDecayAlt.P.B2x8
