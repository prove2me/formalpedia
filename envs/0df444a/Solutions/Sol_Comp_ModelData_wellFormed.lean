-- Prove2me | solution 1 for Comp.ModelData.wellFormed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:07:46.819347+00:00
-- url     : https://prove2.me/submissions/f655b523-4c4e-4c6c-8a36-902d4f44e457

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
import Theorems.Thm_Comp_denseOf_nonneg
import Theorems.Thm_Comp_sum_denseOf

set_option autoImplicit true
open Comp
namespace Comp
namespace ModelData
theorem _root_.solution (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2]
    (hs : d.Shape) (h2 : d.Stochastic) : d.toCsgQ.WellFormed := by
  refine ⟨fun s a1 a2 s' => ?_, fun s a1 a2 => ?_⟩
  · exact denseOf_nonneg _ _ s' (h2 s _ (d.transAt_mem hs s a1 a2)).1
  · change ∑ s' : Fin d.nStates, denseOf d.nStates (d.transAt s a1 a2).dist s' = 1
    rw [sum_denseOf d.nStates _ (d.inRange_transAt hs s a1 a2)]
    exact (h2 s _ (d.transAt_mem hs s a1 a2)).2
end ModelData
end Comp
