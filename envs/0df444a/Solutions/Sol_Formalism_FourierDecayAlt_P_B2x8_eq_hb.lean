-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.eq_hb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:22:47.137336+00:00
-- url     : https://prove2.me/submissions/928555fb-ebc6-4435-9d16-5e0faac62eca

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
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
theorem _root_.solution {y : Fin (2 * r' + k + 1) → ℂ} {b : ℂ} (h : b + conj b = - herm (Hpk k r') y y) : b = hb k r' y b.im := by
  have hr := congrArg Complex.re h
  rw [Complex.add_re, Complex.conj_re, Complex.neg_re] at hr
  apply Complex.ext
  · rw [hb_re]; linarith
  · rw [hb_im]
end Formalism.FourierDecayAlt.P.B2x8
