-- Prove2me | solution 1 for BookProof.SirkCertifiedGap.rayleigh_sectorRestrict
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:09:48.388741+00:00
-- url     : https://prove2.me/submissions/99e8fb56-8c77-46e4-b02c-62d047dd0595

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.rayleigh_sectorRestrict
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

set_option autoImplicit false

theorem solution {T P : E →ₗ[ℂ] E} {s : ℝ} (hcomm : ∀ x, T (P x) = P (T x))
    (y : paritySector P s) : rayleigh (sectorRestrict T P s hcomm) y = rayleigh T (y : E) := by
  rfl

#print axioms solution
