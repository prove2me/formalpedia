-- Prove2me | solution 1 for Formalism.REAL.mem_KG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:42:21.194104+00:00
-- url     : https://prove2.me/submissions/192b0d3a-e4a0-4d87-9d0f-885ea2f411cf

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
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (g : UJ ε) : g ∈ KG ε ↔ toM g ∈ Kset ε := Iff.rfl
end Formalism.REAL
