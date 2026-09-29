-- Prove2me | solution 1 for BookProof.QgHermiteCore.integral_kinetic_symm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:29:37.141327+00:00
-- url     : https://prove2.me/submissions/f1ab20e1-4b3c-4d03-a91a-7905d676929c

-- Generated from ChapterQgHermiteCore.lean — solution of BookProof.QgHermiteCore.integral_kinetic_symm
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
import Theorems.Thm_BookProof_QgHermiteCore_deriv2_gaussPoly
import Theorems.Thm_BookProof_QgHermiteCore_integral_gaussPoly_mul
import Theorems.Thm_BookProof_QgHermiteCore_gint_gaussPolyDeriv_two_symm
open BookProof.QgHermiteCore














open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

set_option maxHeartbeats 1000000 in
theorem solution (p q : Polynomial ℝ) :
    ∫ x : ℝ, gaussPoly p x * (-deriv (deriv (gaussPoly q)) x)
      = ∫ x : ℝ, (-deriv (deriv (gaussPoly p)) x) * gaussPoly q x := by

  rw [deriv2_gaussPoly, deriv2_gaussPoly]
  have hL : ∫ x : ℝ, gaussPoly p x * (-gaussPoly (gaussPolyDeriv (gaussPolyDeriv q)) x)
      = -gint (p * gaussPolyDeriv (gaussPolyDeriv q)) := by
    rw [← integral_gaussPoly_mul, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  have hR : ∫ x : ℝ, (-gaussPoly (gaussPolyDeriv (gaussPolyDeriv p)) x) * gaussPoly q x
      = -gint (gaussPolyDeriv (gaussPolyDeriv p) * q) := by
    rw [← integral_gaussPoly_mul, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [hL, hR, gint_gaussPolyDeriv_two_symm]
