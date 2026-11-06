-- Prove2me | solution 1 for BookProof.EsaOneParticle.positionCore_not_isSelfAdjointOn
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:38:28.4382+00:00
-- url     : https://prove2.me/submissions/5d4783cf-4de9-43c8-8c7f-19da83e6bd04

import Definitions.Def_ChapterEsaOneParticleDGamma

open BookProof.EsaOneParticle
open BookProof.ChapterStoneSeparable
open BookProof.ChapterUnboundedPosition
open BookProof.ChapterUnitaryTransport
open BookProof.ChapterContinuityUnitaryInfinite

theorem solution : ¬ IsSelfAdjointOn Dfin positionCore := by
  change ¬ IsSelfAdjointOn Dfin
    (BookProof.GraphCore.restrictOp (mulSA positionField).op
      (Dfin_le_mulDomain positionField))
  have hle : Dfin ≤ (mulSA positionField).domain := Dfin_le_mulDomain positionField
  have hne : Dfin ≠ (mulSA positionField).domain := Dfin_ne_mulDomain
  let Hs : BookProof.TensorCore.IPSpace := ⟨L2Z⟩
  exact not_isSelfAdjointOn_restrict (Hs := Hs) (mulSA positionField) hle hne
