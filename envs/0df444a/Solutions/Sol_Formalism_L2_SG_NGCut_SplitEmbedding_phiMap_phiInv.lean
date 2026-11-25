-- Prove2me | solution 1 for Formalism.L2.SG.NGCut.SplitEmbedding.phiMap_phiInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:18:08.427725+00:00
-- url     : https://prove2.me/submissions/b3e645cd-6638-4b05-bdc7-7f5842afae82

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_CosetFd
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_MeasurablePhiInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise
open MeasureTheory NumberField NumberField.mixedEmbedding
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NGCut Formalism.L2.SG.NGCut.SplitEmbedding
variable {K : Type} [Field K] [NumberField K] [IsEmpty {w : InfinitePlace K // w.IsReal}] {ι : Type} [Fintype ι]
  (σ : ι ≃ {w : InfinitePlace K // w.IsComplex}) (cj : ι → Prop) [DecidablePred cj]
namespace Formalism.L2.SG.NGCut.SplitEmbedding
theorem _root_.solution (v : ι → ℂ) : phiMap σ cj (phiInv σ cj v) = v := by
  funext i
  by_cases h : cj i <;> simp [phiMap, phiInv, h]
end Formalism.L2.SG.NGCut.SplitEmbedding
