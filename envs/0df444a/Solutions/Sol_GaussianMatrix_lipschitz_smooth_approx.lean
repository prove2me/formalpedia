-- Prove2me | solution 1 for GaussianMatrix.lipschitz_smooth_approx
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T07:58:50.640843+00:00
-- url     : https://prove2.me/submissions/851fa309-8497-4fa1-bc58-715f092b84de

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix.SmoothApprox

/-- `√(∑ xᵢ²) ≤ ∑ |xᵢ|`. -/
lemma sqrt_sum_sq_le_sum_abs {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    Real.sqrt (∑ i, x i ^ 2) ≤ ∑ i, |x i| := by
  have h0 : 0 ≤ ∑ i, |x i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  rw [Real.sqrt_le_left h0]
  have : ∑ i, x i ^ 2 = ∑ i, |x i| ^ 2 := by simp [sq_abs]
  rw [this]
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => abs_nonneg _

/-- The Euclidean norm is bounded by `card ι` times the sup norm. -/
lemma sqrt_sum_sq_sub_le {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    Real.sqrt (∑ i, (x i - y i) ^ 2) ≤ Fintype.card ι * dist x y := by
  refine (sqrt_sum_sq_le_sum_abs (fun i => x i - y i)).trans ?_
  calc ∑ i, |x i - y i| ≤ ∑ _i : ι, dist x y := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← Real.dist_eq]; exact dist_le_pi_dist x y i
    _ = Fintype.card ι * dist x y := by simp

end GaussianMatrix.SmoothApprox

open GaussianMatrix

theorem solution {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) (L : ℝ)
    (hLip : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : (ι → ℝ) → ℝ, (∀ n : ℕ, ContDiff ℝ n g) ∧
      (∀ x y, |g x - g y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)) ∧
      ∀ x, |g x - f x| ≤ ε := by
  set C : ℝ := |L| * Fintype.card ι with hC
  have hC0 : 0 ≤ C := by positivity
  have hdist : ∀ x y, dist (f x) (f y) ≤ C * dist x y := by
    intro x y
    rw [Real.dist_eq]
    refine (hLip x y).trans ?_
    refine (mul_le_mul_of_nonneg_right (le_abs_self L) (Real.sqrt_nonneg _)).trans ?_
    rw [hC, mul_assoc]
    exact mul_le_mul_of_nonneg_left (SmoothApprox.sqrt_sum_sq_sub_le x y) (abs_nonneg L)
  have hcont : Continuous f := (LipschitzWith.of_dist_le' hdist).continuous
  set r : ℝ := ε / (C + 1) with hr
  have hr0 : 0 < r := div_pos hε (by linarith)
  have hCr : C * r ≤ ε := by
    rw [hr, mul_div_assoc']
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  let φ : ContDiffBump (0 : ι → ℝ) := ⟨r / 2, r, half_pos hr0, half_lt_self hr0⟩
  set ψ : (ι → ℝ) → ℝ := φ.normed (volume : Measure (ι → ℝ)) with hψ
  set g : (ι → ℝ) → ℝ :=
    convolution ψ f (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure (ι → ℝ)) with hg
  have hloc : LocallyIntegrable f (volume : Measure (ι → ℝ)) := hcont.locallyIntegrable
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) g :=
    φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hloc
  have hgdef : ∀ x, g x = ∫ t, ψ t * f (x - t) := by
    intro x
    rw [hg, convolution_lsmul]
    rfl
  have hint : ∀ x, Integrable (fun t => ψ t * f (x - t)) (volume : Measure (ι → ℝ)) := by
    intro x
    have := (φ.hasCompactSupport_normed (μ := volume)).convolutionExists_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (φ.continuous_normed (μ := volume)) hloc x
    exact this
  refine ⟨g, ?_, ?_, ?_⟩
  · intro n
    exact hsmooth.of_le (by exact_mod_cast le_top)
  · intro x y
    rw [hgdef x, hgdef y, ← integral_sub (hint x) (hint y)]
    have hb : ∀ t, |ψ t * f (x - t) - ψ t * f (y - t)|
        ≤ ψ t * (L * Real.sqrt (∑ i, (x i - y i) ^ 2)) := by
      intro t
      rw [← mul_sub, abs_mul, abs_of_nonneg (φ.nonneg_normed (μ := volume) t)]
      refine mul_le_mul_of_nonneg_left ?_ (φ.nonneg_normed (μ := volume) t)
      have := hLip (x - t) (y - t)
      simpa using this
    calc |∫ t, (ψ t * f (x - t) - ψ t * f (y - t))|
        ≤ ∫ t, |ψ t * f (x - t) - ψ t * f (y - t)| := abs_integral_le_integral_abs
      _ ≤ ∫ t, ψ t * (L * Real.sqrt (∑ i, (x i - y i) ^ 2)) := by
          refine integral_mono ((hint x).sub (hint y)).abs ?_ hb
          exact (φ.integrable_normed (μ := volume)).mul_const _
      _ = L * Real.sqrt (∑ i, (x i - y i) ^ 2) := by
          rw [integral_mul_const, φ.integral_normed (μ := volume), one_mul]
  · intro x
    rw [← Real.dist_eq]
    refine φ.dist_normed_convolution_le hcont.aestronglyMeasurable ?_
    intro y hy
    refine (hdist y x).trans ?_
    refine (mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hy).le hC0).trans ?_
    exact hCr
