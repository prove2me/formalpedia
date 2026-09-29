-- Prove2me | solution 1 for BookProof.QgHermiteCore.integral_hamiltonian_symm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:30:11.982968+00:00
-- url     : https://prove2.me/submissions/3869c158-aa07-41d0-bd0b-1257c5c310d8

-- Generated from ChapterQgHermiteCore.lean — solution of BookProof.QgHermiteCore.integral_hamiltonian_symm
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
import Theorems.Thm_BookProof_QgHermiteCore_deriv2_gaussPoly
import Theorems.Thm_BookProof_QgHermiteCore_integrable_gaussPoly_mul
import Theorems.Thm_BookProof_QgHermiteCore_integral_kinetic_symm
import Theorems.Thm_BookProof_QgHermiteCore_integrable_potential_gaussPoly_mul
open BookProof.QgHermiteCore














open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

set_option maxHeartbeats 1000000 in
theorem solution {W : ℝ → ℝ} (hW : Continuous W) (hWb : ExpBounded W)
    (p q : Polynomial ℝ) :
    ∫ x : ℝ, gaussPoly p x * (-deriv (deriv (gaussPoly q)) x + W x * gaussPoly q x)
      = ∫ x : ℝ, (-deriv (deriv (gaussPoly p)) x + W x * gaussPoly p x) * gaussPoly q x := by

  have hk1 : Integrable (fun x : ℝ => gaussPoly p x * (-deriv (deriv (gaussPoly q)) x)) := by
    rw [deriv2_gaussPoly]
    refine (integrable_gaussPoly_mul p (gaussPolyDeriv (gaussPolyDeriv q))).neg.congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.neg_apply]
    ring
  have hk2 : Integrable (fun x : ℝ => (-deriv (deriv (gaussPoly p)) x) * gaussPoly q x) := by
    rw [deriv2_gaussPoly]
    refine (integrable_gaussPoly_mul (gaussPolyDeriv (gaussPolyDeriv p)) q).neg.congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.neg_apply]
    ring
  have hv1 : Integrable (fun x : ℝ => gaussPoly p x * (W x * gaussPoly q x)) :=
    (integrable_potential_gaussPoly_mul hW hWb p q).congr
      (Filter.Eventually.of_forall fun x => by ring)
  have hv2 : Integrable (fun x : ℝ => (W x * gaussPoly p x) * gaussPoly q x) :=
    (integrable_potential_gaussPoly_mul hW hWb p q).congr
      (Filter.Eventually.of_forall fun x => by ring)
  have e1 : ∫ x : ℝ, gaussPoly p x * (-deriv (deriv (gaussPoly q)) x + W x * gaussPoly q x)
      = (∫ x : ℝ, gaussPoly p x * (-deriv (deriv (gaussPoly q)) x))
        + ∫ x : ℝ, gaussPoly p x * (W x * gaussPoly q x) := by
    rw [← integral_add hk1 hv1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  have e2 : ∫ x : ℝ, (-deriv (deriv (gaussPoly p)) x + W x * gaussPoly p x) * gaussPoly q x
      = (∫ x : ℝ, (-deriv (deriv (gaussPoly p)) x) * gaussPoly q x)
        + ∫ x : ℝ, (W x * gaussPoly p x) * gaussPoly q x := by
    rw [← integral_add hk2 hv2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  have e3 : ∫ x : ℝ, gaussPoly p x * (W x * gaussPoly q x)
      = ∫ x : ℝ, (W x * gaussPoly p x) * gaussPoly q x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [e1, e2, e3, integral_kinetic_symm]
