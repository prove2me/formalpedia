-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x7.haarHPar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:03:26.71816+00:00
-- url     : https://prove2.me/submissions/f234f331-cbde-43bf-8bda-d1dd7285918d

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open B2x7
open Formalism.FourierDecayAlt.P.B2x7
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x7
theorem _root_.solution (k r' : ℕ) : (volume : Measure (HPar k r')).IsAddHaarMeasure := by
  have h1 : (volume : Measure (Fin (2 * r' + k + 1) → ℂ)).IsAddHaarMeasure := by
    rw [volume_pi]; infer_instance
  rw [Measure.volume_eq_prod]; infer_instance
end Formalism.FourierDecayAlt.P.B2x7
