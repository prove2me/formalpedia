-- Prove2me | solution 1 for Formalism.L2.SG.NGCut.SplitEmbedding.measurable_phiInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:18:08.140157+00:00
-- url     : https://prove2.me/submissions/bdedcd31-3d46-423a-958e-7d6a61b86434

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
theorem _root_.solution : Measurable (phiInv σ cj (K := K)) := by
  unfold phiInv
  refine Measurable.prodMk (measurable_pi_lambda _ fun w => isEmptyElim w) (measurable_pi_lambda _ fun w => ?_)
  by_cases h : cj (σ.symm w)
  · simp only [h, ↓reduceIte]
    exact Complex.continuous_conj.measurable.comp (measurable_pi_apply _)
  · simp only [h, ↓reduceIte]
    exact measurable_pi_apply _
end Formalism.L2.SG.NGCut.SplitEmbedding
