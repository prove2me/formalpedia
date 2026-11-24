-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.ae_first_coordinate_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:04:47.920311+00:00
-- url     : https://prove2.me/submissions/4f01a33d-fb25-4c3d-a4b6-470a1ca4c803

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
theorem _root_.solution : ∀ᵐ p : ℂ × HPar k r' ∂(μx.prod (volume : Measure (HPar k r'))), p.1 ≠ 0 := by
  rw [ae_iff]
  have h0 : μx {(0 : ℂ)} = 0 := (withDensity_absolutelyContinuous _ _) (measure_singleton 0)
  have : {p : ℂ × HPar k r' | ¬ p.1 ≠ 0} = {(0 : ℂ)} ×ˢ Set.univ := by ext p; simp
  rw [this, Measure.prod_prod, h0, zero_mul]
end Formalism.FourierDecayAlt.P.B2x8
