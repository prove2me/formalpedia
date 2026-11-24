-- Prove2me | solution 1 for Formalism.REAL.smoothOnGV_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:45:15.087812+00:00
-- url     : https://prove2.me/submissions/e6c812e7-b448-4a97-8deb-46e3ed51b7c4

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothVectorGrowthBound
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementD
import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    SmoothOnGV ε f ↔ SmoothOnG ε f := Iff.rfl
end Formalism.REAL
