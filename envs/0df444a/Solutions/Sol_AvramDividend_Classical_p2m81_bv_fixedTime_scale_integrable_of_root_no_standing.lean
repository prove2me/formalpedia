-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_fixedTime_scale_integrable_of_root_no_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T05:29:29.866408+00:00
-- url     : https://prove2.me/submissions/9c1cd5ea-69d3-4c17-86ee-76ee09c07254

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_scale_global_weighted_exponential_bound
import Theorems.Thm_AvramDividend_Classical_levy_psi_root_shifted_increment_lower
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal
attribute [local instance] Classical.propDecidable
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P F)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (t : ℝ≥0) :
    Integrable (fun ω => W (x + X.X t ω)) P := by
  classical
  let θ : ℝ := φ + 1
  have hθ : 0 ≤ θ := by
    dsimp [θ]; linarith
  have hgap : q < X.ψ θ := by
    have h := levy_psi_root_shifted_increment_lower X q φ 1 hq hφ zero_lt_one hroot
    have hp : 0 < q / φ := div_pos hq hφ
    simp only [mul_one] at h; dsimp [θ]; linarith
  let C : ℝ := Real.exp (θ * (x + 1)) * (X.ψ θ - q)⁻¹
  have hWnonneg : ∀ y : ℝ, 0 ≤ W y := by
    intro y
    by_cases hy : y < 0
    · rw [hW.1 y hy]
    · exact hW.2.1 y (le_of_not_gt hy)
  have hmeas : AEStronglyMeasurable (fun ω => W (x + X.X t ω)) P :=
    ((chat03_scale_function_borel_measurable X q W hW).comp
      (measurable_const.add ((X.adapted t).mono (F.le t) le_rfl))).aestronglyMeasurable
  have hMajorant : Integrable (fun ω => C * Real.exp (θ * X.X t ω)) P :=
    ((X.laplace t θ hθ).1).const_mul C
  apply hMajorant.mono' hmeas
  filter_upwards [] with ω
  have hb := chat03_scale_global_weighted_exponential_bound
    X q W hW θ (x + X.X t ω) hθ hgap
  have hscale :
      W (x + X.X t ω) ≤
        Real.exp (θ * ((x + X.X t ω) + 1)) * (X.ψ θ - q)⁻¹ := by
    have hfactor : 0 ≤ Real.exp (θ * ((x + X.X t ω) + 1)) :=
      (Real.exp_pos _).le
    have hmul := mul_le_mul_of_nonneg_left hb hfactor
    simpa [← mul_assoc, ← Real.exp_add] using hmul
  have heq :
      Real.exp (θ * ((x + X.X t ω) + 1)) * (X.ψ θ - q)⁻¹ =
        C * Real.exp (θ * X.X t ω) := by
    have hr : θ * ((x + X.X t ω) + 1) = θ * (x + 1) + θ * X.X t ω := by ring
    rw [hr, Real.exp_add]
    dsimp [C]
    ring
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hWnonneg _)] using
    hscale.trans_eq heq
