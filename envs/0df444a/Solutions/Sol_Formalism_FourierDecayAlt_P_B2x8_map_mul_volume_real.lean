-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.map_mul_volume_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:04:41.552266+00:00
-- url     : https://prove2.me/submissions/19942587-cfc3-4614-842e-6cd15d5cec9f

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure

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
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (t : ℝ) (ht : t ≠ 0) :
    (volume : Measure ℝ).map (fun s => t * s) = ENNReal.ofReal (|t|⁻¹) • volume := by
  rw [Real.map_volume_mul_left ht, abs_inv]
end Formalism.FourierDecayAlt.P.B2x8
