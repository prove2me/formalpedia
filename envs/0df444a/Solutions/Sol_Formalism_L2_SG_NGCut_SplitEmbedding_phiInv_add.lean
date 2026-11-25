-- Prove2me | solution 1 for Formalism.L2.SG.NGCut.SplitEmbedding.phiInv_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:16:39.899881+00:00
-- url     : https://prove2.me/submissions/dfb7ca23-4ce0-40e1-987c-97dbeeadcc1f

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
theorem _root_.solution (v w : ι → ℂ) : phiInv σ cj (v + w) = phiInv σ cj v + phiInv σ cj w := by
  refine Prod.ext (funext fun w' => isEmptyElim w') (funext fun w' => ?_)
  by_cases h : cj (σ.symm w') <;> simp [phiInv, h]
end Formalism.L2.SG.NGCut.SplitEmbedding
