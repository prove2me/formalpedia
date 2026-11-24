-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.block_action_tensor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:14.21144+00:00
-- url     : https://prove2.me/submissions/6f689593-ffe9-4f67-9094-83965ab73324

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BlockActTensor
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldtensor_blockAct_blockEmb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : BlockActTensor := by
  intro R K _ _ _ S _ k n g
  refine ⟨fun s F => ldtensor_blockAct_blockEmb K g s F, ?_⟩
  intro M M' hMM' P hP
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨fun s => rowAct K (g s) (F s), fun s => hMM' s (F s) (hF s), ?_⟩
    rw [map_prod]
    exact Finset.prod_congr rfl (fun s _ => ldtensor_blockAct_blockEmb K g s (F s))
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [← algebraMap_smul K a x, map_smul, algebraMap_smul]
    exact Submodule.smul_mem _ a hx
end Formalism.GradedWeylDivisibility
