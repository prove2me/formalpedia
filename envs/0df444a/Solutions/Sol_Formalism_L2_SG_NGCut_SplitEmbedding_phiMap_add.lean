-- Prove2me | solution 1 for Formalism.L2.SG.NGCut.SplitEmbedding.phiMap_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:16:44.592092+00:00
-- url     : https://prove2.me/submissions/327e8a2f-2327-4552-abee-82fd1dfe70fe

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_MassSplit
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_PhiMapAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open MeasureTheory NumberField NumberField.mixedEmbedding
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NGCut Formalism.L2.SG.NGCut.SplitEmbedding
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  (σ : ι ≃ {w : InfinitePlace K // w.IsComplex}) (cj : ι → Prop) [DecidablePred cj]
namespace Formalism.L2.SG.NGCut.SplitEmbedding
theorem _root_.solution (x y : mixedSpace K) : phiMap σ cj (x + y) = phiMap σ cj x + phiMap σ cj y := by
  funext i
  by_cases h : cj i <;> simp [phiMap, h]
end Formalism.L2.SG.NGCut.SplitEmbedding
