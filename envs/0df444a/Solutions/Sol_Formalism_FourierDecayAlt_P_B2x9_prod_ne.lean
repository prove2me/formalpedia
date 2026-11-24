-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.prod_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:47:07.793475+00:00
-- url     : https://prove2.me/submissions/a470477b-631a-4a46-89c4-753b7bbf0d68

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x9
theorem _root_.solution {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β) [SFinite ν]
    (h1 : μ ≠ 0) (h2 : ν ≠ 0) : μ.prod ν ≠ 0 := by
  intro h
  have hz : μ.prod ν (Set.univ ×ˢ Set.univ) = 0 := by simp [h]
  rw [Measure.prod_prod, mul_eq_zero, Measure.measure_univ_eq_zero, Measure.measure_univ_eq_zero] at hz
  exact hz.elim h1 h2
end Formalism.FourierDecayAlt.P.B2x9
