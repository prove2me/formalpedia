-- Prove2me | solution 1 for FunctionalInequalities.Poincare.SmoothTest.tendsto_integral_scaled_mul_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:41:05.201312+00:00
-- url     : https://prove2.me/submissions/bf37e964-6b54-4be6-b001-76ffc24fc321

import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_WeakLimit

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
section Cutoff
variable [FiniteDimensional ℝ E]
omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma FunctionalInequalities.Poincare.SmoothTest.scaled_eq_one_of_ceil_le (x : E) (n : ℕ)
    (hR : 0 < (n : ℝ) + 1) (hn : Nat.ceil ‖x‖ ≤ n) :
    Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x = 1 := by
  apply Energy.Euclidean.LipschitzApproximation.scaled_eq_one hR
  calc
    ‖x‖ ≤ (Nat.ceil ‖x‖ : ℝ) := Nat.le_ceil _
    _ ≤ (n : ℝ) := by exact_mod_cast hn
    _ ≤ (n : ℝ) + 1 := by linarith
omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The first and second integrals of the cutoffs `f χ_{n+1}` converge to those of `f`:
`∫ χ_{n+1} f → ∫ f` and `∫ (χ_{n+1} f)² → ∫ f²` (no `L²`-norm convergence is exported). -/
theorem solution {μ : Measure E} [IsFiniteMeasure μ] {f : E → ℝ}
    (hf : MemLp f 2 μ) :
    Tendsto (fun n : ℕ => ∫ x, FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x ∂μ)
        atTop (𝓝 (∫ x, f x ∂μ)) ∧
      Tendsto (fun n : ℕ =>
          ∫ x, (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x) ^ 2 ∂μ)
        atTop (𝓝 (∫ x, f x ^ 2 ∂μ)) := by
    have hmeas₁ : ∀ n : ℕ, AEStronglyMeasurable
        (fun x =>
          FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x) μ := by
      intro n
      have hχ :
          AEStronglyMeasurable
            (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1)) μ :=
        (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.contDiff_scaled
          ((n : ℝ) + 1)).continuous.aestronglyMeasurable
      exact hχ.mul hf.1

    have hbound₁ : ∀ n : ℕ, ∀ᵐ x ∂μ,
        ‖FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x‖
          ≤ ‖f x‖ := by
      intro n
      filter_upwards [] with x
      have hχ₀ :
          0 ≤ FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x :=
        FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled_nonneg
          ((n : ℝ) + 1) x
      have hχ₁ :
          FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x ≤ 1 :=
        FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled_le_one
          ((n : ℝ) + 1) x
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hχ₀]
      exact mul_le_of_le_one_left (norm_nonneg _) hχ₁

    have hlim₁ : ∀ᵐ x ∂μ, Tendsto
        (fun n : ℕ =>
          FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x)
        atTop (𝓝 (f x)) := by
      filter_upwards [] with x
      refine tendsto_atTop_of_eventually_const (i₀ := Nat.ceil ‖x‖) ?_
      intro n hn
      have hR : 0 < (n : ℝ) + 1 := by positivity
      rw [FunctionalInequalities.Poincare.SmoothTest.scaled_eq_one_of_ceil_le x n hR hn]
      simp

    have hfirst :=
      MeasureTheory.tendsto_integral_of_dominated_convergence
        (bound := fun x => ‖f x‖)
        (F_measurable := hmeas₁)
        (bound_integrable := (hf.integrable one_le_two).norm)
        (h_bound := hbound₁)
        (h_lim := hlim₁)

    have hmeas₂ : ∀ n : ℕ, AEStronglyMeasurable
        (fun x =>
          (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x) ^ 2) μ := by
      intro n
      have hχ :
          AEStronglyMeasurable
            (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1)) μ :=
        (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.contDiff_scaled
          ((n : ℝ) + 1)).continuous.aestronglyMeasurable
      exact (hχ.mul hf.1).pow 2

    have hbound₂ : ∀ n : ℕ, ∀ᵐ x ∂μ,
        ‖(FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x) ^ 2‖
          ≤ f x ^ 2 := by
      intro n
      filter_upwards [] with x
      have hχ₀ :
          0 ≤ FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x :=
        FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled_nonneg
          ((n : ℝ) + 1) x
      have hχ₁ :
          FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x ≤ 1 :=
        FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled_le_one
          ((n : ℝ) + 1) x
      have hnorm :
          ‖FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x‖
            ≤ ‖f x‖ := by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hχ₀]
        exact mul_le_of_le_one_left (norm_nonneg _) hχ₁
      rw [norm_pow]
      calc
        ‖FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x‖ ^ 2
            ≤ ‖f x‖ ^ 2 := by
              calc
                ‖FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled
                      ((n : ℝ) + 1) x * f x‖ ^ 2
                    =
                  ‖FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled
                      ((n : ℝ) + 1) x * f x‖ *
                    ‖FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled
                      ((n : ℝ) + 1) x * f x‖ := by ring
                _ ≤ ‖f x‖ *
                    ‖FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled
                      ((n : ℝ) + 1) x * f x‖ :=
                  mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
                _ ≤ ‖f x‖ * ‖f x‖ :=
                  mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
                _ = ‖f x‖ ^ 2 := by ring
        _ = f x ^ 2 := by
          rw [Real.norm_eq_abs, sq_abs]

    have hlim₂ : ∀ᵐ x ∂μ, Tendsto
        (fun n : ℕ =>
          (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x) ^ 2)
        atTop (𝓝 (f x ^ 2)) := by
      filter_upwards [] with x
      refine tendsto_atTop_of_eventually_const (i₀ := Nat.ceil ‖x‖) ?_
      intro n hn
      have hR : 0 < (n : ℝ) + 1 := by positivity
      rw [FunctionalInequalities.Poincare.SmoothTest.scaled_eq_one_of_ceil_le x n hR hn]
      simp

    have hsecond :=
      MeasureTheory.tendsto_integral_of_dominated_convergence
        (bound := fun x => f x ^ 2)
        (F_measurable := hmeas₂)
        (bound_integrable := (memLp_two_iff_integrable_sq hf.1).1 hf)
        (h_bound := hbound₂)
        (h_lim := hlim₂)

    exact ⟨hfirst, hsecond⟩
