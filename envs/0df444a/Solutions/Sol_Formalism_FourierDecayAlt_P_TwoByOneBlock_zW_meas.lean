-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.zW_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:38:02.433877+00:00
-- url     : https://prove2.me/submissions/86820c41-647a-499b-83f1-f20aebf738c2

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoByOneBlock
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.TwoByOneBlock
theorem _root_.solution (k : ℕ) (T T' : ℝ) : Measurable (fun ζ : ℂ => ENNReal.ofReal (zWeight k T T' ζ)) := by
  unfold zWeight
  refine ENNReal.measurable_ofReal.comp (Measurable.ite ?_ ?_ measurable_const)
  · exact measurableSet_le measurable_const Complex.continuous_normSq.measurable
  · exact ((Complex.continuous_normSq.measurable).sub_const _).pow_const _
end Formalism.FourierDecayAlt.P.TwoByOneBlock
