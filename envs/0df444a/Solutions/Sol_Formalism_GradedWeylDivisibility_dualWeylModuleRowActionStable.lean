-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.dualWeylModuleRowActionStable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:47.602874+00:00
-- url     : https://prove2.me/submissions/b72f256d-0825-4d5d-8f6d-1df8f6d3c2bd

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowstLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylRowStable
import Theorems.Thm_Formalism_GradedWeylDivisibility_colAddGen_rowAct
import Theorems.Thm_Formalism_GradedWeylDivisibility_isWH_algHom
import Theorems.Thm_Formalism_GradedWeylDivisibility_rename_rowAct
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowAct_X_isWH
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowst_mem_dualWeyl_iff


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
theorem _root_.solution : DualWeylRowStable := by
  intro R _ r n ν g f hf
  rw [rowst_mem_dualWeyl_iff] at hf ⊢
  obtain ⟨hw, hc⟩ := hf
  refine ⟨isWH_algHom (rowAct R g) (colW r n) (colW r n)
    (rowAct_X_isWH g) hw, ?_⟩
  intro l j hlj
  rw [colAddGen_rowAct, rename_rowAct, hc l j hlj]
end Formalism.GradedWeylDivisibility
