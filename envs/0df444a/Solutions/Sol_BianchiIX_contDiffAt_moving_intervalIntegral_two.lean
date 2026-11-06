-- Prove2me | solution 1 for BianchiIX.contDiffAt_moving_intervalIntegral_two
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:10:53.992341+00:00
-- url     : https://prove2.me/submissions/775d4f4d-c61e-421a-80ed-9ce5cbad4010

import Theorems.Thm_BianchiIX_contDiffAt_intervalIntegral_two
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence

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


/-- A variable endpoint retains two derivatives after rescaling to a fixed compact interval. -/
theorem solution
    {F : E × ℝ → ℝ} {τ : E → ℝ} {x : E} (hτ : ContDiffAt ℝ 2 τ x) (hpos : 0 ≤ τ x)
    (hF : ∀ t ∈ Icc 0 (τ x), ContDiffAt ℝ 2 F (x, t)) :
    ContDiffAt ℝ 2 (fun y => ∫ t in 0..τ y, F (y, t)) x := by
  have hG (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℝ 2 (fun p : E × ℝ => τ p.1 * F (p.1, p.2 * τ p.1)) (x, t) := by
    have htime : t * τ x ∈ Icc 0 (τ x) :=
      ⟨mul_nonneg ht.1 hpos, by simpa using mul_le_mul_of_nonneg_right ht.2 hpos⟩
    have hcτ : ContDiffAt ℝ 2 (fun p : E × ℝ => τ p.1) (x, t) := hτ.comp (x, t) contDiffAt_fst
    have hp : ContDiffAt ℝ 2 (fun p : E × ℝ => (p.1, p.2 * τ p.1)) (x, t) :=
      contDiffAt_fst.prodMk (contDiffAt_snd.mul hcτ)
    exact hcτ.mul ((hF _ htime).comp (x, t) (g := F)
      (f := fun p : E × ℝ => (p.1, p.2 * τ p.1)) hp)
  convert! contDiffAt_intervalIntegral_two (by norm_num : (0 : ℝ) ≤ 1) hG using 1
  ext y
  exact integral_rescale_zero_one (fun t => F (y, t)) (τ y)
