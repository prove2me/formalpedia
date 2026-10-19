-- Prove2me | solution 1 for CompactnessConjecture.proposedFamily_familyExtremal_sixteenth_power_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/7c50372b-820e-45b2-97e8-c7e804c6908b

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_proposedFamilyFree_sixteenth_power_host_bound
import Theorems.Thm_CompactnessConjecture_finiteNatSup_sixteenth_power_le

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution (n : ℕ) :
    (familyExtremal proposedFamily n : ℝ) ^ 16 ≤
      compactnessHostPowerConstant * (n : ℝ) ^ 21 := by
  classical
  have hbound :
      0 ≤ compactnessHostPowerConstant * (n : ℝ) ^ 21 := by
    unfold compactnessHostPowerConstant compactnessDegreePowerConstant
    positivity
  unfold familyExtremal
  apply finiteNatSup_sixteenth_power_le
    (Finset.univ.filter (FamilyFree proposedFamily))
    (fun host : SimpleGraph (Fin n) => host.edgeFinset.card)
    (compactnessHostPowerConstant * (n : ℝ) ^ 21) hbound
  intro host hhost
  exact proposedFamilyFree_sixteenth_power_host_bound n host
    (Finset.mem_filter.mp hhost).2
end CompactnessConjecture
