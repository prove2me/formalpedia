-- Prove2me | solution 1 for ConsistentSubmodular.AtomicProfile.selector_high_anchor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:34:56.50421+00:00
-- url     : https://prove2.me/submissions/7aebdb33-7c83-4bb1-81cb-b02bb27cc25d

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SelectorRelays
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_rawEnvelope_attained
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_actual_test
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_high_anchor_profile_eligible
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_high_anchor_profile_relay

section

open ConsistentSubmodular
open ConsistentSubmodular.AtomicProfile
variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem solution (hP : P.Canonical) (h : Fin (m + 1))
    (S : SelectorState P h) (hq : 1 ≤ P.rawEnvelope h) (hq2 : P.rawEnvelope h ≤ 2)
    (hA : (33 : ℝ) / 40 ≤ P.designated h) :
    Nonempty (CheckpointCertificate P) ∨ ∃ s, h < s ∧ Nonempty (SelectorState P s) := by
  classical
  let q := P.rawEnvelope h
  obtain ⟨s, hs, hd, heq⟩ := P.rawEnvelope_attained h (show 0 < q by dsimp [q]; linarith)
  have hhs : h < s := (Finset.mem_filter.mp hs).2.1
  have ha : P.Active s := (Finset.mem_filter.mp hs).2.2
  have helig := P.high_anchor_profile_eligible hP h s hhs.le hA S.credit q hq hq2 hd heq
  rcases P.actual_test hP h S.access q hq hq2 (P.selector_envelope hP h) with hyes | hno
  · exact Or.inl hyes
  · have hf := hno s hhs ha helig
    obtain ⟨hsafe, hhigh, _⟩ := P.high_anchor_profile_relay hP h s hhs hA S.below_unit
      S.credit q hq hd heq hf
    right
    exact ⟨s, hhs, ⟨P.relayState hP h s S hhs ha hq hd heq hsafe hhigh
      (fun _ => hno) (fun hn => False.elim (not_lt_of_ge hq2 hn)) (fun _ => hA)⟩⟩

end
