-- Prove2me | solution 1 for FairSelling.Examples.MMS_example
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:50:28.314693+00:00
-- url     : https://prove2.me/submissions/bbb08e29-8999-4f56-b8f2-3c72bc382eea

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_Examples
import Theorems.Thm_FairSelling_Examples_TPS_example
import Theorems.Thm_FairSelling_MMS_le_TPS_le_PS
import Theorems.Thm_FairSelling_le_MMS_of_outcome
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.Examples
namespace FairSelling.Examples
theorem _root_.solution : MMS 2 vex pex = 1 := by
  have hv : ∀ g, 0 ≤ vex g := by
    intro g; fin_cases g <;> norm_num [vex]
  have hp : ∀ g, 0 ≤ pex g := by
    intro g; fin_cases g <;> norm_num [pex]
  refine le_antisymm ?_ ?_
  · have h := (MMS_le_TPS_le_PS vex pex (n := 2) (by norm_num) hv hp).1
    rw [TPS_example] at h
    exact h
  · -- give the first good to agent `0` and the second to agent `1`
    refine le_MMS_of_outcome (by norm_num) vex pex hv hp
      ⟨∅, fun j => {j}, fun _ => 0⟩ ?_ 1 ?_
    · refine ⟨fun _ => by simp, fun j k hjk => by simpa using hjk, fun _ => le_refl 0, by simp⟩
    · intro j
      fin_cases j <;> simp [util] <;> norm_num [vex]
end FairSelling.Examples
