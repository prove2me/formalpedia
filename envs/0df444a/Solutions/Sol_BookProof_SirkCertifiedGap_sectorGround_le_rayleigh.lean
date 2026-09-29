-- Prove2me | solution 1 for BookProof.SirkCertifiedGap.sectorGround_le_rayleigh
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:16:20.393775+00:00
-- url     : https://prove2.me/submissions/23fb73e3-ba5f-4be7-af18-2b42b8f2df2e

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.sectorGround_le_rayleigh
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

set_option autoImplicit false

private theorem sirkR_rayleigh_bddBelow (T P : E →ₗ[ℂ] E) (s : ℝ) :
    BddBelow (sectorRayleighSet T P s) := by
  refine ⟨-‖T.toContinuousLinearMap‖, ?_⟩
  rintro r ⟨x, hx, hmem, rfl⟩
  have hn : ‖T x‖ ≤ ‖T.toContinuousLinearMap‖ := by
    simpa only [LinearMap.coe_toContinuousLinearMap', hx, mul_one] using T.toContinuousLinearMap.le_opNorm x
  have hi : |rayleigh T x| ≤ ‖x‖ * ‖T x‖ :=
    (Complex.abs_re_le_norm _).trans (norm_inner_le_norm x (T x))
  rw [hx, one_mul] at hi
  exact (abs_le.mp (hi.trans hn)).1

theorem solution {T : E →ₗ[ℂ] E} {P : E →ₗ[ℂ] E} {s : ℝ}
    (hT : T.IsSymmetric) {x : E} (hx : ‖x‖ = 1) (hmem : x ∈ paritySector P s) :
    sectorGround T P s ≤ rayleigh T x := by
  apply csInf_le (sirkR_rayleigh_bddBelow T P s)
  exact ⟨x, hx, hmem, rfl⟩

#print axioms solution
