-- Prove2me | solution 2 for BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.ext_prime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-16T19:45:46.812987+00:00
-- url     : https://prove2.me/submissions/0667bbbd-d5a3-4495-a751-e924f526a26e

-- Generated from ChapterStoneTheorem.lean — solution of BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.ext'
import Mathlib
import Definitions.Def_ChapterStoneTheorem
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneResolvent
open BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint



open scoped InnerProductSpace


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option maxHeartbeats 1000000 in
theorem solution : ∀ {T S : UnboundedSelfAdjoint H}, T.domain = S.domain →
    (∀ (x : H) (hx : x ∈ T.domain) (hx' : x ∈ S.domain), T.op ⟨x, hx⟩ = S.op ⟨x, hx'⟩) → T = S
  | ⟨_, _, _, _, _⟩, ⟨_, _, _, _, _⟩, hd, ho => by
      subst hd
      simp only [UnboundedSelfAdjoint.mk.injEq, heq_eq_eq, true_and]
      ext x
      exact ho (x : H) x.2 x.2
