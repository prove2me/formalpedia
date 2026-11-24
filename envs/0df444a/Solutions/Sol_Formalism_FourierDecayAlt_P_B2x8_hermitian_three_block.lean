-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.hermitian_three_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:29:15.00708+00:00
-- url     : https://prove2.me/submissions/0e75a119-2647-4cd1-9f31-80472401b458

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_first
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_middle
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_tk_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_hermitian_matrix_three_block

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
theorem _root_.solution (a a' b b' : ℂ) (y y' : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) (mk3 k r' a y b) (mk3 k r' a' y' b') =
      a * conj b' + b * conj a' + herm (Hpk k r') y y' := by
  unfold herm
  rw [hermitian_matrix_three_block]
  simp only [dotProduct, Pi.star_apply]
  rw [tk_sum]
  have e1 : ∀ (a : ℂ) y (b : ℂ), mk3 k r' a y b (tkF k r') = a := fun a y b => three_block_first a y b
  have e2 : ∀ (a : ℂ) y (b : ℂ) j, mk3 k r' a y b (levPos k 1 r' j) = y j :=
    fun a y b j => congrFun (three_block_middle a y b) j
  have e3 : ∀ (a : ℂ) y (b : ℂ), mk3 k r' a y b (tkL k r') = b := fun a y b => three_block_last a y b
  simp only [e1, e2, e3, starRingEnd_apply]
  ring
end Formalism.FourierDecayAlt.P.B2x8
