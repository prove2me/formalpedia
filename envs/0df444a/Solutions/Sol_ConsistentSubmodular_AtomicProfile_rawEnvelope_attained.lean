-- Prove2me | solution 1 for ConsistentSubmodular.AtomicProfile.rawEnvelope_attained
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:22.263214+00:00
-- url     : https://prove2.me/submissions/501005a6-7493-414e-8d0a-8da80d88dbee

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Envelope

section

open ConsistentSubmodular
open ConsistentSubmodular.AtomicProfile
variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem solution (h : Fin (m + 1)) (hq : 0 < P.rawEnvelope h) :
    ∃ t, t ∈ P.laterActive h ∧ 0 < P.designated h - P.residual h t ∧
      P.rawRatio h t = P.rawEnvelope h := by
  classical
  have hmem : P.rawEnvelope h ∈ P.ratioSet h := Finset.max'_mem _ _
  rcases Finset.mem_insert.mp hmem with hz | ht
  · linarith
  · obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp ht
    refine ⟨t, ht, ?_, heq⟩
    have hd := P.raw_denominator_nonnegative h t
      (le_of_lt (Finset.mem_filter.mp ht).2.1)
    by_contra hn
    have hz : P.designated h - P.residual h t = 0 := le_antisymm (le_of_not_gt hn) hd
    rw [rawRatio, hz, div_zero] at heq
    linarith

end
