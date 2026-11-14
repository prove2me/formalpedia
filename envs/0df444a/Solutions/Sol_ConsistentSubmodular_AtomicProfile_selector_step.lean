-- Prove2me | solution 1 for ConsistentSubmodular.AtomicProfile.selector_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:39:14.255199+00:00
-- url     : https://prove2.me/submissions/edca7882-2e56-4b82-8616-03bee5b0da9b

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SelectorRelays
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_VertexCheckpoint
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_actual_test
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_checkpoint_of_baseline_stop
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_selector_large_parameter
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_selector_high_anchor
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_selector_low_parameter
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_middle_parameter_checkpoint

section

open ConsistentSubmodular
open ConsistentSubmodular.AtomicProfile
variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem solution (hP : P.Canonical) (h : Fin (m + 1)) (S : SelectorState P h) :
    Nonempty (CheckpointCertificate P) ∨ ∃ s, h < s ∧ Nonempty (SelectorState P s) := by
  by_cases hnonpos : P.rawEnvelope h ≤ 0
  · exact Or.inl ⟨P.checkpoint_of_nonpositive hP h S.high.le S.credit S.access hnonpos⟩
  have hpos : 0 < P.rawEnvelope h := lt_of_not_ge hnonpos
  by_cases hlow : P.rawEnvelope h ≤ 1
  · exact Or.inl (P.selector_low_parameter hP h S hpos hlow)
  have hq1 : 1 ≤ P.rawEnvelope h := (lt_of_not_ge hlow).le
  by_cases hlarge : (4 : ℝ) / 3 ≤ P.rawEnvelope h
  · exact P.selector_large_parameter hP h S hlarge
  have hq4 : P.rawEnvelope h < 4 / 3 := lt_of_not_ge hlarge
  by_cases hhigh : (33 : ℝ) / 40 ≤ P.designated h
  · exact P.selector_high_anchor hP h S hq1 (by linarith) hhigh
  by_cases hbase : 3 * (1 - P.designated h) ≤ P.baseline h
  · exact Or.inl (P.checkpoint_of_baseline_stop hP h S.high S.access hbase hq1 (by linarith))
  rcases P.actual_test hP h S.access (P.rawEnvelope h) hq1 (by linarith)
      (P.selector_envelope hP h) with hyes | hno
  · exact Or.inl hyes
  · exact Or.inl (P.middle_parameter_checkpoint hP h S hq1 hq4
      (lt_of_not_ge hhigh) (lt_of_not_ge hbase) hno)

end
