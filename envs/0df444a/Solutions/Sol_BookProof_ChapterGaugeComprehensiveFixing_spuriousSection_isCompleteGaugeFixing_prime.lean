-- Prove2me | solution 1 for BookProof.ChapterGaugeComprehensiveFixing.spuriousSection_isCompleteGaugeFixing_prime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:28:27.922332+00:00
-- url     : https://prove2.me/submissions/69cfaa50-a7c8-464c-9d0c-1f5f29b30621

-- Generated from ChapterGaugeComprehensiveFixing.lean — solution of BookProof.ChapterGaugeComprehensiveFixing.spuriousSection_isCompleteGaugeFixing'
import Mathlib
import Definitions.Def_ChapterGaugeComprehensiveFixing
open BookProof.ChapterGaugeComprehensiveFixing




open BookProof.ChapterGaugeIncompleteFixing

variable {X : Type*} (G : Type*) [Group G] [MulAction G X]
variable {X : Type*} {G : Type*} [Group G] [MulAction G X] {S : Set X}
variable {X : Type*} [TopologicalSpace X] {G : Type*} [Group G] [MulAction G X]
variable (X : Type*) (G : Type*) [Group G] [MulAction G X]

set_option maxHeartbeats 1000000 in
theorem solution :
    IsCompleteGaugeFixing' G (spuriousSection X G) := by

  rintro ⟨x, hx⟩ hxS ⟨y, hy⟩ hyS g hg
  have hx1 : hx = 1 := hxS
  have hy1 : hy = 1 := hyS
  subst hx1; subst hy1
  have hg2 : g * (1 : G) = 1 := congrArg Prod.snd hg
  have hg1 : g = 1 := by simpa using hg2
  subst hg1
  have hfst : x = y := by simpa using congrArg Prod.fst hg
  rw [hfst]
