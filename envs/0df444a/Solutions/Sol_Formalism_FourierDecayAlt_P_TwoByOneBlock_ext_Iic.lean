-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.ext_Iic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:31:15.53822+00:00
-- url     : https://prove2.me/submissions/4647ab97-38d8-4ee7-be11-50f4b1b5b0f6

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
theorem _root_.solution (μ ν : Measure ℝ) (h : ∀ b, μ (Iic b) = ν (Iic b)) (hf : ∀ b, μ (Iic b) ≠ ∞) : μ = ν := by
  refine Measure.ext_of_Ioc' μ ν (fun a b _ => ne_top_of_le_ne_top (hf b) (measure_mono Ioc_subset_Iic_self))
    (fun a b hab => ?_)
  rw [← Iic_sdiff_Iic, measure_sdiff (Iic_subset_Iic.2 hab.le) nullMeasurableSet_Iic (hf a),
    measure_sdiff (Iic_subset_Iic.2 hab.le) nullMeasurableSet_Iic (h a ▸ hf a), h a, h b]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
