-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.cf_hb_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:19:52.594923+00:00
-- url     : https://prove2.me/submissions/1f7a9a82-f5f6-4191-88b6-bead2f9a9990

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
theorem _root_.solution (y : Fin (2 * r' + k + 1) → ℂ) (s : ℝ) : hb k r' y (-s) = conj (hb k r' y s) := by
  apply Complex.ext
  · rw [Complex.conj_re, hb_re, hb_re]
  · rw [Complex.conj_im, hb_im, hb_im]
end Formalism.FourierDecayAlt.P.B2x8
