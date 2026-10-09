-- Prove2me | solution 1 for BookProof.ChapterCayleyTransform.cayley_shift
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:04:20.093008+00:00
-- url     : https://prove2.me/submissions/f4fbca7d-731e-40c1-a765-81bf8a25f0c0

-- Generated from ChapterCayleyTransform.lean — solution of BookProof.ChapterCayleyTransform.cayley_shift
import Mathlib
import Definitions.Def_ChapterCayleyTransform
open BookProof.ChapterCayleyTransform



open scoped InnerProductSpace
open Filter Topology


open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)

set_option maxHeartbeats 1000000 in
theorem solution (x : T.domain) : cayley T (T.shift (-1) x) = T.shift 1 x := cayleyMap_shift T x
