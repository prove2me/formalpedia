-- Prove2me | solution 1 for ConsistentSubmodular.AtomicProfile.last_suff_partner
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:30.953644+00:00
-- url     : https://prove2.me/submissions/12728a3f-3635-42dd-b777-c566d7bbe9fc

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Envelope

section

open ConsistentSubmodular
open ConsistentSubmodular.AtomicProfile
variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem solution (h s : Fin (m + 1)) (q : ℝ)
    (hs : s ∈ P.laterActive h) (he : 0 ≤ P.suffEligibility h q s) :
    ∃ c, c ∈ P.laterActive h ∧ s ≤ c ∧ 0 ≤ P.suffEligibility h q c ∧
      ∀ t, c < t → P.Active t → P.suffEligibility h q t < 0 := by
  classical
  let eligible := (P.laterActive h).filter (fun t => 0 ≤ P.suffEligibility h q t)
  have hne : eligible.Nonempty := ⟨s, Finset.mem_filter.mpr ⟨hs, he⟩⟩
  let c := eligible.max' hne
  have hc : c ∈ eligible := Finset.max'_mem _ _
  have hcle := Finset.le_max' eligible s (Finset.mem_filter.mpr ⟨hs, he⟩)
  refine ⟨c, (Finset.mem_filter.mp hc).1, hcle, (Finset.mem_filter.mp hc).2, ?_⟩
  intro t hct ht
  by_contra hn
  have htelig : t ∈ eligible := by
    refine Finset.mem_filter.mpr ⟨?_, le_of_not_gt hn⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      lt_trans (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).2.1 hct, ht⟩
  exact (not_le_of_gt hct) (Finset.le_max' eligible t htelig)

end
