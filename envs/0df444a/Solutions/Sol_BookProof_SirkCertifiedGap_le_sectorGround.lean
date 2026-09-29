-- Prove2me | solution 1 for BookProof.SirkCertifiedGap.le_sectorGround
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:12:22.091498+00:00
-- url     : https://prove2.me/submissions/63db5f2e-2b90-47e6-b776-73d2179905b9

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.le_sectorGround
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

set_option autoImplicit false

theorem solution {T P : E →ₗ[ℂ] E} {s c : ℝ}
    (hne : (sectorRayleighSet T P s).Nonempty)
    (hlb : ∀ x : E, ‖x‖ = 1 → x ∈ paritySector P s → c ≤ rayleigh T x) :
    c ≤ sectorGround T P s := by
  apply le_csInf hne
  rintro r ⟨x, hx, hmem, rfl⟩
  exact hlb x hx hmem

#print axioms solution
