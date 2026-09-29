-- Prove2me | solution 1 for BookProof.SirkCertifiedGap.sectorRayleighSet_bddBelow
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:16:19.215558+00:00
-- url     : https://prove2.me/submissions/23d81b8e-55bd-447b-9ac0-e7f4cb33e92b

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.sectorRayleighSet_bddBelow
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

set_option autoImplicit false

theorem solution {T : E →ₗ[ℂ] E} (P : E →ₗ[ℂ] E) (s : ℝ)
    (hT : T.IsSymmetric) : BddBelow (sectorRayleighSet T P s) := by
  refine ⟨-‖T.toContinuousLinearMap‖, ?_⟩
  rintro r ⟨x, hx, hmem, rfl⟩
  have hn : ‖T x‖ ≤ ‖T.toContinuousLinearMap‖ := by
    simpa only [LinearMap.coe_toContinuousLinearMap', hx, mul_one] using T.toContinuousLinearMap.le_opNorm x
  have hi : |rayleigh T x| ≤ ‖x‖ * ‖T x‖ :=
    (Complex.abs_re_le_norm _).trans (norm_inner_le_norm x (T x))
  rw [hx, one_mul] at hi
  exact (abs_le.mp (hi.trans hn)).1

#print axioms solution
