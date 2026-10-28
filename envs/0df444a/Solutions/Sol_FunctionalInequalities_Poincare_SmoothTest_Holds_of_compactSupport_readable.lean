-- Prove2me | solution 1 for FunctionalInequalities.Poincare.SmoothTest.Holds.of_compactSupport_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:43:29.96429+00:00
-- url     : https://prove2.me/submissions/fb44215b-55ac-40fa-929f-4f2b23d413bd

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_WeakLimit
import Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_Admissible_of_contDiff_hasCompactSupport_readable
import Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_tendsto_energy_scaled_mul_readable
import Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_tendsto_integral_scaled_mul_readable

section
noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff ENNReal
section
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section FiniteDimensional
variable [FiniteDimensional ℝ E]
theorem FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.hasCompactSupport_scaled {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (scaled (E := E) R) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : E) (2 * R)) fun x hx =>
    scaled_eq_zero hR (by
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      exact le_of_lt (not_le.mp hx))
end FiniteDimensional
end
end
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
section Cutoff
variable [FiniteDimensional ℝ E]
/-- **A Poincaré bound on compactly supported admissible tests extends to all admissible tests**
(BKL Section 2, cutoff extension). -/
theorem solution {μ : Measure E} [IsProbabilityMeasure μ] {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ f : E → ℝ, FunctionalInequalities.Poincare.SmoothTest.Admissible μ f → HasCompactSupport f → variance f μ ≤ C * FunctionalInequalities.Poincare.SmoothTest.energy μ f) :
    FunctionalInequalities.Poincare.SmoothTest.Holds μ C := by
    refine
      { probability := inferInstance
        constant_nonneg := hC
        variance_le := ?_ }
    intro f hf
    let χ (n : ℕ) : E → ℝ :=
      FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1)
    let g (n : ℕ) : E → ℝ := fun x => χ n x * f x
    have hadm (n : ℕ) : FunctionalInequalities.Poincare.SmoothTest.Admissible μ (g n) := by
      change
        FunctionalInequalities.Poincare.SmoothTest.Admissible μ
          (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) * f)
      exact
        FunctionalInequalities.Poincare.SmoothTest.Admissible.of_contDiff_hasCompactSupport_readable
          ((FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.contDiff_scaled _).mul hf.smooth')
          ((FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.hasCompactSupport_scaled
            (by positivity)).mul_right)
    have hcs (n : ℕ) : HasCompactSupport (g n) := by
      change
        HasCompactSupport
          (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) * f)
      exact
        (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.hasCompactSupport_scaled
          (by positivity)).mul_right
    have hlim :=
      FunctionalInequalities.Poincare.SmoothTest.tendsto_integral_scaled_mul_readable (μ := μ) hf.memLp_two
    have h1 :
        Tendsto
          (fun n : ℕ => ∫ x, χ n x * f x ∂μ)
          atTop (𝓝 (∫ x, f x ∂μ)) := by
      simpa [χ] using hlim.1
    have h2 :
        Tendsto
          (fun n : ℕ => ∫ x, (χ n x * f x) ^ 2 ∂μ)
          atTop (𝓝 (∫ x, f x ^ 2 ∂μ)) := by
      simpa [χ] using hlim.2
    have hv :
        (fun n : ℕ => variance (g n) μ) =
          (fun n : ℕ =>
            (∫ x, (χ n x * f x) ^ 2 ∂μ) -
              (∫ x, χ n x * f x ∂μ) ^ 2) := by
      funext n
      rw [variance_eq_sub (hadm n).memLp_two]
      rfl
    have hvar :
        Tendsto (fun n : ℕ => variance (g n) μ)
          atTop (𝓝 (variance f μ)) := by
      rw [hv, variance_eq_sub hf.memLp_two]
      exact h2.sub (h1.pow 2)
    have henergy :
        Tendsto (fun n : ℕ => C * FunctionalInequalities.Poincare.SmoothTest.energy μ (g n))
          atTop (𝓝 (C * FunctionalInequalities.Poincare.SmoothTest.energy μ f)) := by
      have hE :
          Tendsto (fun n : ℕ => FunctionalInequalities.Poincare.SmoothTest.energy μ (g n))
            atTop (𝓝 (FunctionalInequalities.Poincare.SmoothTest.energy μ f)) := by
        simpa [g, χ] using (FunctionalInequalities.Poincare.SmoothTest.tendsto_energy_scaled_mul_readable (μ := μ) hf)
      simpa using hE.const_mul C
    exact
      le_of_tendsto_of_tendsto' hvar henergy
        (fun n => h (g n) (hadm n) (hcs n))
