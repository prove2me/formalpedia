-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.hb_add_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:34:58.203796+00:00
-- url     : https://prove2.me/submissions/ac5ffcb1-99c3-4d59-8cd4-97c8f24857e8

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_self_im
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_hb_re
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_hb_im

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
theorem _root_.solution (y : Fin (2 * r' + k + 1) → ℂ) (s : ℝ) :
    hb k r' y s + conj (hb k r' y s) = - herm (Hpk k r') y y := by
  apply Complex.ext
  · rw [Complex.add_re, Complex.conj_re, hb_re, Complex.neg_re]; ring
  · rw [Complex.add_im, Complex.conj_im, hb_im, Complex.neg_im, herm_self_im]; ring
end Formalism.FourierDecayAlt.P.B2x8
