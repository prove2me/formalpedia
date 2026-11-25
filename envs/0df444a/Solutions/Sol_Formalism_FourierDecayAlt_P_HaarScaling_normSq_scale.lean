-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HaarScaling.normSq_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:30:55.027587+00:00
-- url     : https://prove2.me/submissions/3842d07f-5d95-4bfa-b591-8fe6e4fb478d

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaBOfComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HaarScaling

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HaarScaling
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
variable [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.HaarScaling
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (c : ℝ≥0) (hc : 0 < c) (F : Mat k r → (Wq →L[ℂ] Wp)) :
    normSq (scaleG D c hc) F = normSq D F := rfl
end Formalism.FourierDecayAlt.P.HaarScaling
