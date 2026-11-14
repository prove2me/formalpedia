-- Prove2me | solution 1 for ConsistentSubmodular.AtomicProfile.actual_test
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:28:12.640941+00:00
-- url     : https://prove2.me/submissions/284126f7-ae06-4221-a711-62e3e2e232db

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Access
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_ActualCheckpoint
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_last_actual_partner

section

open ConsistentSubmodular
open ConsistentSubmodular.AtomicProfile
variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem solution (hP : P.Canonical) (h : Fin (m + 1))
    (access : AccessCertificate P h) (q : ℝ) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (henv : ∀ t, h < t → P.Active t → 0 ≤ P.envelopeSlack h q t) :
    Nonempty (CheckpointCertificate P) ∨
      ∀ t, h < t → P.Active t → 0 ≤ P.actualEligibility h q t →
        q * (P.benchmark t - P.designated h) <
          2 * P.designated h * q - 3 * (4 * P.designated h - 3) := by
  classical
  by_cases hex : ∃ s, s ∈ P.laterActive h ∧ 0 ≤ P.actualEligibility h q s
  · obtain ⟨s, hs, he⟩ := hex
    obtain ⟨c, hc, _, hec, hlast⟩ := P.last_actual_partner h s q hs he
    have hhc : h < c := (Finset.mem_filter.mp hc).2.1
    by_cases hcredit : 2 * P.designated h * q - 3 * (4 * P.designated h - 3) ≤
        q * (P.benchmark c - P.designated h)
    · left
      exact ⟨P.checkpoint_of_actual_middle hP h c hhc q hq1 hq2 hec henv
        (fun t hct ha => (hlast t hct ha).le) hcredit
        access.entry access.initial access.terminal access.safe access.pieces⟩
    · right
      intro t _ ht he
      have htc : t ≤ c := by
        by_contra hn
        have := hlast t (lt_of_not_ge hn) ht
        linarith
      have hm := mul_le_mul_of_nonneg_left (P.benchmark_monotone hP htc)
        (show 0 ≤ q by linarith)
      linarith
  · right
    intro t hht ht he
    exact False.elim (hex ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hht, ht⟩, he⟩)

end
