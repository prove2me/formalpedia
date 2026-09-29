-- Prove2me | solution 1 for BookProof.SirkCertifiedGap.certified_parity_gap_of_data
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:16:17.737355+00:00
-- url     : https://prove2.me/submissions/aa1507f9-0ff6-4bf8-b8e7-095db0883b3d

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.certified_parity_gap_of_data
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

theorem solution {T P : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    {vE : E} (hvE : ‖vE‖ = 1) (hvEmem : vE ∈ paritySector P 1)
    {thetaE thetaO deltaE deltaO : ℝ} (hthetaE : rayleigh T vE = thetaE) (hdE : 0 ≤ deltaE)
    (hOdd : thetaO - deltaO ≤ sectorGround T P (-1)) :
    thetaO - thetaE - (deltaO + deltaE) ≤ sectorGround T P (-1) - sectorGround T P 1 := by
  have hEven0 : sectorGround T P 1 ≤ rayleigh T vE :=
    csInf_le (sirkR_rayleigh_bddBelow T P 1) ⟨vE, hvE, hvEmem, rfl⟩
  linarith

#print axioms solution
