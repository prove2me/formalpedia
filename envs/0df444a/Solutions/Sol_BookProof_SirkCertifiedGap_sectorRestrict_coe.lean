-- Prove2me | solution 1 for BookProof.SirkCertifiedGap.sectorRestrict_coe
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:09:41.32844+00:00
-- url     : https://prove2.me/submissions/f28e34f3-f8b2-439f-8de3-5734ab240aac

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.sectorRestrict_coe
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

set_option autoImplicit false

theorem solution {T P : E →ₗ[ℂ] E} {s : ℝ} (hcomm : ∀ x, T (P x) = P (T x))
    (y : paritySector P s) : ((sectorRestrict T P s hcomm) y : E) = T (y : E) := by
  rfl

#print axioms solution
