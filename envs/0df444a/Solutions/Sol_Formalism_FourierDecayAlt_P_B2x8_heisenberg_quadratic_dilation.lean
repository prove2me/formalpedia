-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.heisenberg_quadratic_dilation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:04:53.552732+00:00
-- url     : https://prove2.me/submissions/996518a9-8536-4119-a5be-48512407952b

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_smul_right

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
theorem _root_.solution (c : ℂ) (y : Fin (2 * r' + k + 1) → ℂ) (s : ℝ) :
    hb k r' (c • y) (‖c‖ ^ 2 * s) = ((‖c‖ ^ 2 : ℝ) : ℂ) * hb k r' y s := by
  unfold hb
  rw [herm_smul_left, herm_smul_right]
  have h : (c * (conj c * herm (Hpk k r') y y)).re = ‖c‖ ^ 2 * (herm (Hpk k r') y y).re := by
    rw [← mul_assoc, Complex.mul_conj, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]
  rw [h]
  push_cast
  ring
end Formalism.FourierDecayAlt.P.B2x8
