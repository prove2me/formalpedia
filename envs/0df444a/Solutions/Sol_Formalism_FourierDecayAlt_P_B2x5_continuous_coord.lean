-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.continuous_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:47:31.189598+00:00
-- url     : https://prove2.me/submissions/34a24574-479c-416a-86df-9a6baeb3ace0

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x5
theorem _root_.solution (k r' : ℕ) : Continuous (coord k r') := by
  unfold coord
  first
  | fun_prop
  | exact Continuous.prodMk (continuous_pi fun j => (continuous_apply _).comp (continuous_apply _))
      (Complex.continuous_im.comp ((continuous_apply _).comp (continuous_apply _)))
end Formalism.FourierDecayAlt.P.B2x5
