-- Prove2me | solution 1 for ConsistentSubmodular.AtomicProfile.low_actual_test
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:28:13.809384+00:00
-- url     : https://prove2.me/submissions/c72541d0-401e-4ad1-83c0-8303b493d0f6

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Access
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_ActualCheckpoint
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_last_actual_partner

section

open ConsistentSubmodular
open ConsistentSubmodular.AtomicProfile
variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem solution (hP : P.Canonical) (h : Fin (m + 1))
    (hA : (3 : ℝ) / 4 ≤ P.designated h) (hcredit : P.StrongCredit h)
    (access : AccessCertificate P h) (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (henv : ∀ t, h < t → P.Active t → 0 ≤ P.envelopeSlack h q t) :
    Nonempty (CheckpointCertificate P) ∨
      ∀ t, h < t → P.Active t → P.actualEligibility h q t < 0 := by
  classical
  by_cases hex : ∃ s, s ∈ P.laterActive h ∧ 0 ≤ P.actualEligibility h q s
  · obtain ⟨s, hs, he⟩ := hex
    obtain ⟨c, hc, _, hec, hlast⟩ := P.last_actual_partner h s q hs he
    have hhc : h < c := (Finset.mem_filter.mp hc).2.1
    have hbase := P.strongCredit_baseline hP h hA hcredit
    have hA1 := P.designated_le_one hP h
    have hbudget : 3 ≤ P.designated h + 2 * P.benchmark h := by
      unfold benchmark
      linarith
    left
    exact ⟨P.checkpoint_of_actual_low hP h c hhc q hq hq1 hec henv
      (fun t hct ha => (hlast t hct ha).le) hbudget
      access.entry access.initial access.terminal access.safe access.pieces⟩
  · right
    intro t hht ht
    by_contra hn
    exact hex ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hht, ht⟩, le_of_not_gt hn⟩

end
