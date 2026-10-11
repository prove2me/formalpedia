-- Prove2me | solution 1 for BookProof.SmOneParticle.smPhi_injective
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T19:50:18.896181+00:00
-- url     : https://prove2.me/submissions/9416cfc1-b149-4a60-96b0-fb0959f22963

-- Generated from ChapterSmOneParticle.lean — theorem BookProof.SmOneParticle.smPhi_injective
import Mathlib
import Definitions.Def_ChapterSmOneParticle
open BookProof.SmOneParticle
open BookProof.SmOneParticle

theorem solution: Function.Injective smPhi := by
  intro a b h
  unfold smPhi at h
  have := smIdx.injective h
  simpa using this
