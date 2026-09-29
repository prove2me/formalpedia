-- Prove2me | solution 1 for BookProof.SirkCertifiedGap.sectorRestrict_isSymmetric
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:12:20.60343+00:00
-- url     : https://prove2.me/submissions/20a2f6d6-559e-4211-8638-7bfbd6de061c

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.sectorRestrict_isSymmetric
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

set_option autoImplicit false

theorem solution {T P : E →ₗ[ℂ] E} {s : ℝ}
    (hcomm : ∀ x, T (P x) = P (T x)) (hT : T.IsSymmetric) :
    (sectorRestrict T P s hcomm).IsSymmetric := by
  intro x y
  exact hT (x : E) (y : E)

#print axioms solution
