-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.prod_swap_measure_preserving
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:04:52.105507+00:00
-- url     : https://prove2.me/submissions/a65bc615-4f87-4934-a547-cc5e7b472b5c

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
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] : MeasurePreserving Prod.swap (μ.prod ν) (ν.prod μ) := Measure.measurePreserving_swap
end Formalism.FourierDecayAlt.P.B2x8
