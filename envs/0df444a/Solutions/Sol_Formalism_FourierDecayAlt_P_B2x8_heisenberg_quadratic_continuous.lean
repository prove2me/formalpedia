-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.heisenberg_quadratic_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:04:52.692005+00:00
-- url     : https://prove2.me/submissions/a98c188d-4945-4298-bbee-759970324d9d

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
theorem _root_.solution : Continuous fun q : HPar k r' => hb k r' q.1 q.2 := by
  have h := hermitian_quadratic_continuous (k := k) (r' := r')
  unfold hb
  exact (Complex.continuous_ofReal.comp ((Complex.continuous_re.comp (h.comp continuous_fst)).neg.div_const 2)).add ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
end Formalism.FourierDecayAlt.P.B2x8
