-- Prove2me | solution 1 for BitcoinTapSoundnessV2.tagged_collision
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T18:05:39.487003+00:00
-- url     : https://prove2.me/submissions/79071264-ca3c-4df2-ac71-d60118dcbd71

import Definitions.Def_BitcoinTapSoundnessV2
import Theorems.Thm_BitcoinSer_sha256_length
import Theorems.Thm_BitcoinTapSoundnessV2_tagged_pre

open BitcoinTapSoundnessV2 BitcoinSer BitcoinTaproot

private theorem append_inj_len {α : Type} (a b c d : List α) (hl : a.length = c.length) (h : a ++ b = c ++ d) :
    a = c ∧ b = d :=
  List.append_inj h hl

/-- Equal tagged hashes have equal tags' hashes and equal messages, or their two preimages collide. -/
theorem solution (t t' : String) (m m' : BitcoinSer.Bytes)
    (h : BitcoinTaproot.tagged t m = BitcoinTaproot.tagged t' m') :
    (BitcoinSer.sha256 (BitcoinSig.ascii t) = BitcoinSer.sha256 (BitcoinSig.ascii t') ∧ m = m') ∨
      BitcoinTapSoundnessV2.Collides (BitcoinTapSoundnessV2.taggedPre t m) (BitcoinTapSoundnessV2.taggedPre t' m') := by
  rw [tagged_pre, tagged_pre] at h
  by_cases heq : taggedPre t m = taggedPre t' m'
  · left
    unfold taggedPre at heq
    have hl : (sha256 (BitcoinSig.ascii t) ++ sha256 (BitcoinSig.ascii t)).length =
        (sha256 (BitcoinSig.ascii t') ++ sha256 (BitcoinSig.ascii t')).length := by
      simp only [List.length_append, BitcoinSer.sha256_length]
    obtain ⟨h1, h2⟩ := append_inj_len _ _ _ _ hl heq
    obtain ⟨h3, -⟩ := append_inj_len _ _ _ _ (by simp only [BitcoinSer.sha256_length]) h1
    exact ⟨h3, h2⟩
  · right; exact ⟨heq, h⟩
