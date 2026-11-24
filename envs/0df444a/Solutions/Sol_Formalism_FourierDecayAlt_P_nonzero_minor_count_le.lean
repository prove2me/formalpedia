-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.nonzero_minor_count_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:44:07.199588+00:00
-- url     : https://prove2.me/submissions/8153611a-c90b-4b68-93a7-f8b5035a2b3c

import Definitions.Def_Formalism_HermitianCurvature_LemmaDensOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DensityLemmaOfReductions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) : Formalism.FourierDecayAlt.DensityAveraging.nzMin D γ ≤ r + 2 := by
  unfold Formalism.FourierDecayAlt.DensityAveraging.nzMin
  calc _ ≤ (Finset.univ : Finset (Fin (r + 2))).card := Finset.card_filter_le _ _
    _ = r + 2 := by simp
end Formalism.FourierDecayAlt.P
