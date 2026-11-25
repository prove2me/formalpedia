-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxI.ckOn_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:32:08.950422+00:00
-- url     : https://prove2.me/submissions/9bd24eba-177a-4ce2-9107-6492987801f1

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfBetaAdjCOfLemmaBNorm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellDiagonalMap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellInversePair
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordIntegralScaling
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothWordsAll
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliUnderIntegral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfExhaustOfAvgCutoff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxI
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.JFxI
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {U V : Set (Mat k r)}
    (hUV : U ⊆ V) {f : Mat k r → E} (h : CkOn m V f) : CkOn m U f := by
  exact fun g₀ hg => h g₀ (hUV hg)
end Formalism.FourierDecayAlt.P.JFxI
