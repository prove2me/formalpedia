-- Prove2me | solution 1 for BianchiIX.hasFDerivAt_moving_intervalIntegral_of_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:07:48.198274+00:00
-- url     : https://prove2.me/submissions/567a479e-cceb-45b1-908f-db861f948579

import Theorems.Thm_BianchiIX_hasFDerivAt_intervalIntegral_of_contDiffAt
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem BianchiIX.integral_rescale_zero_one (f : ℝ → ℝ) (b : ℝ) :
    (∫ t in 0..b, f t) = ∫ t in (0 : ℝ)..1, b * f (t * b) := by
  rw [intervalIntegral.integral_const_mul]
  simpa only [smul_eq_mul, zero_mul, one_mul] using
    (intervalIntegral.smul_integral_comp_mul_right (a := (0 : ℝ)) (b := 1) f b).symm

end
end

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


/-- Rescaling differentiates a moving endpoint together with the integrand. -/
theorem solution
    {F : E × ℝ → ℝ} {τ : E → ℝ} {x : E} (hτ : ContDiffAt ℝ 1 τ x) (hpos : 0 ≤ τ x)
    (hF : ∀ t ∈ Icc 0 (τ x), ContDiffAt ℝ 1 F (x, t)) :
    HasFDerivAt (fun y => ∫ t in 0..τ y, F (y, t))
      (∫ t in (0 : ℝ)..1,
        (fderiv ℝ (fun p : E × ℝ => τ p.1 * F (p.1, p.2 * τ p.1)) (x, t)).comp
          (ContinuousLinearMap.inl ℝ E ℝ)) x := by
  have hG (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℝ 1 (fun p : E × ℝ => τ p.1 * F (p.1, p.2 * τ p.1)) (x, t) := by
    have htime : t * τ x ∈ Icc 0 (τ x) :=
      ⟨mul_nonneg ht.1 hpos, by simpa using mul_le_mul_of_nonneg_right ht.2 hpos⟩
    have hcτ : ContDiffAt ℝ 1 (fun p : E × ℝ => τ p.1) (x, t) :=
      hτ.comp (x, t) contDiffAt_fst
    have hp : ContDiffAt ℝ 1 (fun p : E × ℝ => (p.1, p.2 * τ p.1)) (x, t) :=
      contDiffAt_fst.prodMk (contDiffAt_snd.mul hcτ)
    have hcomp := (hF _ htime).comp (x, t) (g := F)
      (f := fun p : E × ℝ => (p.1, p.2 * τ p.1)) hp
    exact hcτ.mul hcomp
  convert! hasFDerivAt_intervalIntegral_of_contDiffAt (by norm_num : (0 : ℝ) ≤ 1) hG using 1
  ext y
  exact integral_rescale_zero_one (fun t => F (y, t)) (τ y)
