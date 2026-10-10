-- Prove2me | solution 1 for BookProof.ChapterIPin.ipin_left
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:11:27.860455+00:00
-- url     : https://prove2.me/submissions/ac812f33-be7a-48fd-a1c3-9e1f3dfe8532

-- Generated from ChapterIPin.lean — solution of BookProof.ChapterIPin.ipin_left
import Mathlib
import Definitions.Def_ChapterIPin
open BookProof.ChapterIPin




open Multiplicative

variable {P V : Type*} [Group P] [AddCommGroup V] (Λ : P →* Multiplicative (AddAut V))

variable {P V : Type*} [Group P] [AddCommGroup V] (Λ : P →* Multiplicative (AddAut V))

set_option maxHeartbeats 1000000 in
theorem solution (Λ : P →* Multiplicative (AddAut V)) (x y : IPin Λ) :
    toAdd (x * y).left = toAdd x.left + Multiplicative.toAdd (Λ x.right) (toAdd y.left) := by

  refine (congrArg toAdd (SemidirectProduct.mul_left x y)).trans ?_
  show toAdd (Multiplicative.ofAdd (toAdd x.left + toAdd (phiHom Λ x.right y.left))) = _
  simp only [toAdd_ofAdd]
  congr 1
