-- Prove2me | solution 2 for BookProof.SirkCertifiedGap.sectorRestrict_coe
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-29T19:47:52.980844+00:00
-- url     : https://prove2.me/submissions/bdb9dcdf-9cff-4256-8fb7-792b98e4b9d5

-- Generated from ChapterSirkCertifiedGap.lean — solution of BookProof.SirkCertifiedGap.sectorRestrict_coe
import Mathlib
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap



noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution {T P : E →ₗ[ℂ] E} {s : ℝ} (hcomm : ∀ x, T (P x) = P (T x))
    (y : paritySector P s) : ((sectorRestrict T P s hcomm) y : E) = T (y : E) := rfl
