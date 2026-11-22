-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_future_window_killed_scale_integrable_no_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T05:09:02.422817+00:00
-- url     : https://prove2.me/submissions/36231c4f-4e02-4644-8ffe-12b33a5f48f6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_scale_global_weighted_exponential_bound
import Theorems.Thm_AvramDividend_Classical_levy_psi_root_shifted_increment_lower
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_shifted_lower_closed_event_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_lower_killing_future_window_reindex
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal
attribute [local instance] Classical.propDecidable
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) :
    Integrable
      (({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
        (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
          W (x + X.X u ω))) P := by
  classical
  have hWin := chat04_lower_killing_future_window_reindex X x s u hsu
  have hB : MeasurableSet {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
      0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)} := by
    rw [hWin]
    exact avram_root29_01_shifted_lower_closed_event_measurable X x s (u - s)
  have hSc : Integrable (fun ω => W (x + X.X u ω)) P := by
    let θ : ℝ := φ + 1
    have hθ : 0 ≤ θ := by
      dsimp [θ]
      linarith
    have hgap : q < X.ψ θ := by
      have h := levy_psi_root_shifted_increment_lower
        X q φ 1 hq hφ zero_lt_one hroot
      have hp : 0 < q / φ := div_pos hq hφ
      simp only [mul_one] at h
      dsimp [θ]
      linarith
    let C : ℝ := Real.exp (θ * (x + 1)) * (X.ψ θ - q)⁻¹
    have hWnonneg : ∀ y : ℝ, 0 ≤ W y := by
      intro y
      by_cases hy : y < 0
      · rw [hW.1 y hy]
      · exact hW.2.1 y (le_of_not_gt hy)
    have hmeas : AEStronglyMeasurable (fun ω => W (x + X.X u ω)) P :=
      ((chat03_scale_function_borel_measurable X q W hW).comp
        (measurable_const.add ((X.adapted u).mono (𝓕.le u) le_rfl))).aestronglyMeasurable
    have hMajorant : Integrable (fun ω => C * Real.exp (θ * X.X u ω)) P :=
      ((X.laplace u θ hθ).1).const_mul C
    apply hMajorant.mono' hmeas
    filter_upwards [] with ω
    have hb := chat03_scale_global_weighted_exponential_bound
      X q W hW θ (x + X.X u ω) hθ hgap
    have hscale :
        W (x + X.X u ω) ≤
          Real.exp (θ * ((x + X.X u ω) + 1)) * (X.ψ θ - q)⁻¹ := by
      have hfactor : 0 ≤ Real.exp (θ * ((x + X.X u ω) + 1)) :=
        (Real.exp_pos _).le
      have hmul := mul_le_mul_of_nonneg_left hb hfactor
      simpa [← mul_assoc, ← Real.exp_add] using hmul
    have heq :
        Real.exp (θ * ((x + X.X u ω) + 1)) * (X.ψ θ - q)⁻¹ =
          C * Real.exp (θ * X.X u ω) := by
      have hr : θ * ((x + X.X u ω) + 1) = θ * (x + 1) + θ * X.X u ω := by
        ring
      rw [hr, Real.exp_add]
      dsimp [C]
      ring
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hWnonneg _)] using
      hscale.trans_eq heq
  exact (hSc.const_mul (Real.exp (-(q * ((u : ℝ) - (s : ℝ)))))).indicator hB
