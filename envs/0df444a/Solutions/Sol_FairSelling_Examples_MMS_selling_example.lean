-- Prove2me | solution 1 for FairSelling.Examples.MMS_selling_example
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:50:07.529388+00:00
-- url     : https://prove2.me/submissions/798fc1fe-c58a-4dff-a59e-8c6955250fef

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_Examples
import Theorems.Thm_FairSelling_MMS_le_TPS_le_PS
import Theorems.Thm_FairSelling_le_MMS_of_outcome
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.Examples
namespace FairSelling.Examples
theorem _root_.solution : MMS 2 vsell psell = 1 := by
  have hv : ∀ g, 0 ≤ vsell g := by
    intro g; fin_cases g; norm_num [vsell]
  have hp : ∀ g, 0 ≤ psell g := by
    intro g; fin_cases g; norm_num [psell]
  refine le_antisymm ?_ ?_
  · -- `MMS ≤ TPS ≤ PS = 1`
    have h := MMS_le_TPS_le_PS vsell psell (n := 2) (by norm_num) hv hp
    have hPS : PS 2 vsell psell = 1 := by
          simp [PS, vsell, psell]
    linarith [h.1, h.2, hPS.le, hPS.ge]
  · -- sell the good and give each agent half of the proceeds
    refine le_MMS_of_outcome (by norm_num) vsell psell hv hp
      ⟨Finset.univ, fun _ => ∅, fun _ => 1⟩ ?_ 1 ?_
    · refine ⟨fun _ => by simp, fun _ _ _ => by simp, fun _ => by norm_num, ?_⟩
      simp [psell]
    · intro j; simp [util]
end FairSelling.Examples
