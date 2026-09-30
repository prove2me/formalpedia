-- Prove2me | solution 2 for BookProof.SirkCertifiedGap.sectorRestrict_isSymmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-29T19:53:11.576612+00:00
-- url     : https://prove2.me/submissions/18a5a124-7660-4695-af67-86b68cd4d03e

-- Generated from ChapterSirkCertifiedGap.lean — solution of BookProof.SirkCertifiedGap.sectorRestrict_isSymmetric
import Mathlib
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap



noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution {T P : E →ₗ[ℂ] E} {s : ℝ}
    (hcomm : ∀ x, T (P x) = P (T x)) (hT : T.IsSymmetric) :
    (sectorRestrict T P s hcomm).IsSymmetric := by

  intro x y
  simpa [sectorRestrict, Submodule.coe_inner] using hT x.val y.val
