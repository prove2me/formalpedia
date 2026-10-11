-- Prove2me | solution 1 for BookProof.ChapterUnitaryTransport.transported_position_isSelfAdjointOn
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:16:33.939237+00:00
-- url     : https://prove2.me/submissions/786253fc-949e-4952-9764-603791377bdd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterUnitaryTransport.lean — solution of BookProof.ChapterUnitaryTransport.transported_position_isSelfAdjointOn
import Mathlib
import Definitions.Def_ChapterUnitaryTransport
import Theorems.Thm_BookProof_ChapterUnitaryTransport_transport_isSelfAdjointOn
import Theorems.Thm_BookProof_ChapterUnitaryTransport_mulOp_isSelfAdjointOn
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterUnboundedPosition
open BookProof.ChapterUnitaryTransport



open scoped InnerProductSpace
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterF7
open BookProof.ChapterUnboundedPosition


variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

set_option maxHeartbeats 1000000 in

theorem solution (f : ℤ → ℝ) (W : L2Z ≃ₗᵢ[ℂ] K) :
    IsSelfAdjointOn (transportDomain W (mulDomain f)) (transportOp W (mulDomain f) (mulOp f)) :=
  transport_isSelfAdjointOn W _ _ (mulOp_isSelfAdjointOn f)
