-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.heisenberg_coordinate_measurable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:04:51.860082+00:00
-- url     : https://prove2.me/submissions/fbf334e8-425f-449d-92ba-b6363520147c

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_hermitian_quadratic_continuous

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
theorem _root_.solution : Measurable (fun x : HPar k r' => hb k r' x.1 x.2) := by
  have h := hermitian_quadratic_continuous (k := k) (r' := r')
  refine Continuous.measurable ?_
  unfold hb
  exact (Complex.continuous_ofReal.comp ((Complex.continuous_re.comp (h.comp continuous_fst)).neg.div_const 2)).add ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
end Formalism.FourierDecayAlt.P.B2x8
