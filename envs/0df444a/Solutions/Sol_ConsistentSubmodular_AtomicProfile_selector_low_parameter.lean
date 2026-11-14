-- Prove2me | solution 1 for ConsistentSubmodular.AtomicProfile.selector_low_parameter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:27.248623+00:00
-- url     : https://prove2.me/submissions/792bee46-a51e-4a04-8487-51b6162018ef

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SelectorRelays
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_rawEnvelope_attained
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_low_actual_test
import Theorems.Thm_ConsistentSubmodular_LowRollback_low_parameter_checkpoint
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_threshold_profile_eligible
import Theorems.Thm_ConsistentSubmodular_RelayHistory_child_threshold_of_small_parameter

section

open ConsistentSubmodular
open ConsistentSubmodular.AtomicProfile
variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem solution (hP : P.Canonical) (h : Fin (m + 1))
    (S : SelectorState P h) (hq0 : 0 < P.rawEnvelope h) (hq1 : P.rawEnvelope h ≤ 1) :
    Nonempty (CheckpointCertificate P) := by
  classical
  rcases P.low_actual_test hP h S.high.le S.credit S.access (P.rawEnvelope h)
      hq0 hq1 (P.selector_envelope hP h) with hyes | hno
  · exact hyes
  · obtain ⟨s, hs, hd, heq⟩ := P.rawEnvelope_attained h hq0
    have hhs : h < s := (Finset.mem_filter.mp hs).2.1
    have ha : P.Active s := (Finset.mem_filter.mp hs).2.2
    have hanchor : P.designated h < 1281 / 1600 := by
      by_contra hn
      have he := P.threshold_profile_eligible hP h s hhs.le (le_of_not_gt hn)
        S.credit (P.rawEnvelope h) hq0 hq1 hd heq
      linarith [hno s hhs ha]
    have hparent : 4 / 3 ≤ S.history.parameter := by
      by_contra hn
      have hh := S.history.child_threshold_of_small_parameter hP (lt_of_not_ge hn)
      linarith
    exact LowRollback.low_parameter_checkpoint P hP h S hparent hanchor hq0 hq1 hno

end
