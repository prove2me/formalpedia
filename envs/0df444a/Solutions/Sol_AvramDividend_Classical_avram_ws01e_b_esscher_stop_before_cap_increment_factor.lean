-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_esscher_stop_before_cap_increment_factor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T00:14:49.084711+00:00
-- url     : https://prove2.me/submissions/e02cdf77-ee6d-4a9b-a27d-1cb98066b300

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_esscher_locally_bounded_stop_increment_cylinder_factor

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hStop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H u T : ℝ≥0) (hT : H + 1 + u ≤ T)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
      ({ω : Ω | τ ω ≤ H} ∩ {ω : Ω |
        X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}) =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
        {ω : Ω | τ ω ≤ H} *
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
      ((X.X u) ⁻¹' B) := by
  have hA : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] ({ω : Ω | τ ω ≤ H} ∩ {ω : Ω | τ ω ≤ s}) := by
    intro s
    have h1 : {ω : Ω | τ ω ≤ H} ∩ {ω : Ω | τ ω ≤ s} = {ω : Ω | ((τ ω : ℝ≥0) : WithTop ℝ≥0) ≤ ((min H s : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω; simp only [mem_inter_iff, mem_setOf_eq]; rw [WithTop.coe_le_coe, le_min_iff]
    rw [h1]
    exact 𝓕.mono (min_le_right H s) _ (hStop (min H s))
  exact esscher_locally_bounded_stop_increment_cylinder_factor X θ hθ τ hStop H u T hT
    {ω : Ω | τ ω ≤ H} hA (fun ω h => h) B hB
