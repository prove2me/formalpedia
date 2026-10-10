-- Prove2me | solution 1 for BookProof.ChapterIPin.ipin_right
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:11:26.776142+00:00
-- url     : https://prove2.me/submissions/a019c243-1a83-4f51-ad77-d2fd4bb50153

-- Generated from ChapterIPin.lean — solution of BookProof.ChapterIPin.ipin_right
import Mathlib
import Definitions.Def_ChapterIPin
open BookProof.ChapterIPin




open Multiplicative

variable {P V : Type*} [Group P] [AddCommGroup V] (Λ : P →* Multiplicative (AddAut V))

variable {P V : Type*} [Group P] [AddCommGroup V] (Λ : P →* Multiplicative (AddAut V))

set_option maxHeartbeats 1000000 in
theorem solution (Λ : P →* Multiplicative (AddAut V)) (x y : IPin Λ) :
    (x * y).right = x.right * y.right := SemidirectProduct.mul_right x y
