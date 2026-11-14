-- Prove2me | solution 1 for ConsistentSubmodular.AtomicProfile.checkpoint_of_selector_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:42.405732+00:00
-- url     : https://prove2.me/submissions/499b11aa-9e19-4b4d-a156-f24bdda34b88

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SelectorState

section

open ConsistentSubmodular
open ConsistentSubmodular.AtomicProfile
variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem solution
    (step : ∀ h, SelectorState P h → Nonempty (CheckpointCertificate P) ∨
      ∃ s, h < s ∧ Nonempty (SelectorState P s))
    (h : Fin (m + 1)) (S : SelectorState P h) : Nonempty (CheckpointCertificate P) := by
  have claim : ∀ r : ℕ, ∀ h : Fin (m + 1), m - h.val = r →
      Nonempty (SelectorState P h) → Nonempty (CheckpointCertificate P) := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro h heq ⟨S⟩
      rcases step h S with hdone | ⟨s, hhs, hs⟩
      · exact hdone
      · exact ih (m - s.val) (by have := s.isLt; change h.val < s.val at hhs; omega)
          s rfl hs
  exact claim (m - h.val) h rfl ⟨S⟩

end
