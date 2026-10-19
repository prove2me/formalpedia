-- Prove2me | solution 1 for CauchyRiemannIndex.exists_plane_cutoff_family
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T11:50:27.650331+00:00
-- url     : https://prove2.me/submissions/8ba09737-dd2b-4452-8715-538bd50730e4

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct



namespace CauchyRiemannIndex

open scoped ContDiff

/-- Cutoff family: `c R z = b (R⁻¹ • z)` for a fixed bump `b` equal to `1` on the unit ball. -/
theorem exists_plane_cutoff_family_aux :
    ∃ (c : ℝ → ℂ → ℂ) (M : ℝ), 0 ≤ M ∧ ∀ R > 0,
      ContDiff ℝ ∞ (c R) ∧ HasCompactSupport (c R) ∧
      (∀ z, (starRingEnd ℂ) (c R z) = c R z) ∧
      (∀ z, ‖z‖ ≤ R → c R z = 1) ∧
      (∀ z, ‖fderiv ℝ (c R) z‖ ≤ M / R) := by
  let b : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hbd : Continuous fun z => fderiv ℝ b z :=
    (b.contDiff (n := 1)).continuous_fderiv one_ne_zero
  obtain ⟨M, hM⟩ := hbd.bounded_above_of_compact_support (b.hasCompactSupport.fderiv (𝕜 := ℝ))
  refine ⟨fun R z => ((b (R⁻¹ • z) : ℝ) : ℂ), M, le_trans (norm_nonneg _) (hM 0), ?_⟩
  intro R hR
  have hRi : R⁻¹ ≠ 0 := inv_ne_zero hR.ne'
  have hder : ∀ z, HasFDerivAt (fun z : ℂ => ((b (R⁻¹ • z) : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((fderiv ℝ b (R⁻¹ • z)).comp
        (R⁻¹ • ContinuousLinearMap.id ℝ ℂ))) z := by
    intro z
    have h1 : HasFDerivAt (fun z : ℂ => R⁻¹ • z) (R⁻¹ • ContinuousLinearMap.id ℝ ℂ) z :=
      (hasFDerivAt_id (𝕜 := ℝ) z).const_smul R⁻¹
    have h2 := (((b.contDiff (n := 1)).differentiable one_ne_zero) (R⁻¹ • z)).hasFDerivAt.comp z h1
    exact Complex.ofRealCLM.hasFDerivAt.comp z h2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp (b.contDiff.comp
      (contDiff_const_smul _))
  · exact (b.hasCompactSupport.comp_smul hRi).comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  · intro z; simp
  · intro z hz
    have : R⁻¹ • z ∈ Metric.closedBall (0 : ℂ) b.rIn := by
      simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_pos hR]
      show R⁻¹ * ‖z‖ ≤ 1
      rw [inv_mul_le_iff₀ hR]; linarith
    show ((b (R⁻¹ • z) : ℝ) : ℂ) = 1
    rw [b.one_of_mem_closedBall this]; simp
  · intro z
    rw [(hder z).fderiv]
    calc ‖Complex.ofRealCLM.comp ((fderiv ℝ b (R⁻¹ • z)).comp (R⁻¹ • ContinuousLinearMap.id ℝ ℂ))‖
        ≤ ‖Complex.ofRealCLM‖ * (‖fderiv ℝ b (R⁻¹ • z)‖ * ‖R⁻¹ • ContinuousLinearMap.id ℝ ℂ‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (M * R⁻¹) := by
          have h1 : ‖Complex.ofRealCLM‖ ≤ 1 :=
            ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simp)
          have h3 : ‖R⁻¹ • ContinuousLinearMap.id ℝ ℂ‖ ≤ R⁻¹ := by
            refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hR.le) (fun x => ?_)
            simp [norm_smul, abs_of_pos hR]
          have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
          exact mul_le_mul h1 (mul_le_mul (hM _) h3 (norm_nonneg _) hM0)
            (by positivity) zero_le_one
      _ = M / R := by ring

end CauchyRiemannIndex

open CauchyRiemannIndex

open scoped ContDiff

theorem solution :
    ∃ (c : ℝ → ℂ → ℂ) (M : ℝ), 0 ≤ M ∧ ∀ R > 0,
      ContDiff ℝ ∞ (c R) ∧ HasCompactSupport (c R) ∧
      (∀ z, (starRingEnd ℂ) (c R z) = c R z) ∧
      (∀ z, ‖z‖ ≤ R → c R z = 1) ∧
      (∀ z, ‖fderiv ℝ (c R) z‖ ≤ M / R) :=
  exists_plane_cutoff_family_aux
