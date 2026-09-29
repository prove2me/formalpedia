-- Prove2me | solution 1 for BookProof.ChapterSirkTrotterKato.ofBounded_op
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T10:26:13.446839+00:00
-- url     : https://prove2.me/submissions/f3ec0d43-fc63-4ea6-b75b-d58a54ca3073

-- Generated from ChapterSirkTrotterKatoGalerkin.lean — solution of BookProof.ChapterSirkTrotterKato.ofBounded_op
import Mathlib
import Definitions.Def_ChapterSirkTrotterKatoGalerkin
open BookProof.ChapterSirkTrotterKato









noncomputable section

open Filter Topology


open BookProof.ChapterStoneResolvent BookProof.ChapterUnitaryTransport

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option maxHeartbeats 1000000 in
theorem solution (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (x : H)
    (hx : x ∈ (ofBounded A hA).domain) : (ofBounded A hA).op ⟨x, hx⟩ = A x := rfl
