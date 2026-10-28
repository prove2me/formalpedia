-- Prove2me | solution 1 for BitcoinHeader.version_floor
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:37:14.94861+00:00
-- url     : https://prove2.me/submissions/69550c47-bd31-4b77-8b1c-5413408bb558

import Definitions.Def_BitcoinHeader
import Theorems.Thm_BitcoinHeader_contextualCheck_iff

open BitcoinHeader

/-- After each soft fork's activation height, the corresponding version floor holds for every
accepted header. -/
theorem solution (h : BitcoinHeader.Header) (prevHeight : Nat) (prevTimes : List Int)
    (required : BitVec 32) (now : Int)
    (hc : BitcoinHeader.contextualCheck h prevHeight prevTimes required now = true) :
    (BitcoinHeader.BIP34Height ≤ prevHeight + 1 → 2 ≤ h.version) ∧
    (BitcoinHeader.BIP66Height ≤ prevHeight + 1 → 3 ≤ h.version) ∧
    (BitcoinHeader.BIP65Height ≤ prevHeight + 1 → 4 ≤ h.version) := by
  obtain ⟨-, -, -, hv⟩ := (BitcoinHeader.contextualCheck_iff h prevHeight prevTimes required now).1 hc
  refine ⟨fun h34 => ?_, fun h66 => ?_, fun h65 => ?_⟩
  · rcases Int.lt_or_le h.version 2 with hlt | hge
    · exact absurd (Or.inl ⟨hlt, h34⟩) hv
    · exact hge
  · rcases Int.lt_or_le h.version 3 with hlt | hge
    · exact absurd (Or.inr (Or.inl ⟨hlt, h66⟩)) hv
    · exact hge
  · rcases Int.lt_or_le h.version 4 with hlt | hge
    · exact absurd (Or.inr (Or.inr ⟨hlt, h65⟩)) hv
    · exact hge
