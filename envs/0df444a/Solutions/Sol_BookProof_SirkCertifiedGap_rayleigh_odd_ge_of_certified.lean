-- Prove2me | solution 1 for BookProof.SirkCertifiedGap.rayleigh_odd_ge_of_certified
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:16:18.520878+00:00
-- url     : https://prove2.me/submissions/a57e4173-e7e7-4297-a7c9-f635a8b755b3

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.rayleigh_odd_ge_of_certified
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

theorem solution {T P : E →ₗ[ℂ] E} {thetaE thetaO deltaE deltaO : ℝ}
    (hT : T.IsSymmetric)
    (hEven : sectorGround T P 1 ≤ thetaE + deltaE)
    (hOdd : thetaO - deltaO ≤ sectorGround T P (-1))
    {x : E} (hx : ‖x‖ = 1) (hmem : x ∈ paritySector P (-1)) :
    sectorGround T P 1 + (thetaO - thetaE - (deltaO + deltaE)) ≤ rayleigh T x := by
  have hxbound : sectorGround T P (-1) ≤ rayleigh T x :=
    csInf_le (sirkR_rayleigh_bddBelow T P (-1)) ⟨x, hx, hmem, rfl⟩
  linarith

#print axioms solution
