-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.zW_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:49:23.189114+00:00
-- url     : https://prove2.me/submissions/b1e1cba6-1397-4fda-8df5-ba9b03b950ae

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RankOneEmbeddings Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
theorem _root_.solution (k : ℕ) (T T' : ℝ) : Measurable (zWeight k T T') := by
  unfold zWeight
  exact Measurable.ite (measurableSet_le measurable_const Complex.continuous_normSq.measurable)
    ((Complex.continuous_normSq.measurable.sub_const _).pow_const _) measurable_const
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
