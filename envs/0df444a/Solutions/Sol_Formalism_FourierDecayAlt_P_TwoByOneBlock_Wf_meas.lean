-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.Wf_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:52:40.960842+00:00
-- url     : https://prove2.me/submissions/00181996-82e6-4327-8fe1-1a0e9fe547c7

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
open Set
open scoped Pointwise
namespace Formalism.FourierDecayAlt.P.TwoByOneBlock
theorem _root_.solution (n : ℕ) (T T' : ℝ) {φ : ℂ → ℝ≥0∞} (hφ : Measurable φ) : Measurable (Wf n T T' φ) := by
  unfold Wf
  refine Measurable.indicator ?_ (measurableSet_lt measurable_const Complex.continuous_normSq.measurable)
  exact (ENNReal.measurable_ofReal.comp ((Complex.continuous_normSq.measurable.sub_const _).pow_const _)).mul hφ
end Formalism.FourierDecayAlt.P.TwoByOneBlock
