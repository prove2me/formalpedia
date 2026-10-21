-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_scale_fixed_time_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T04:33:06.059985+00:00
-- url     : https://prove2.me/submissions/657cca8d-1746-4b81-90a6-3623494aa10f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_gaussian
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_infinite_small_jump_moment
import Theorems.Thm_AvramDividend_Classical_unbounded_variation_gaussian_or_infinite_small_jump_moment
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_scale_global_weighted_exponential_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (x : ℝ) (t : ℝ≥0) :
    Integrable (fun ω => W (x + X.X t ω)) P := by
  -- Unbounded variation splits into the Gaussian case and the
  -- infinite-small-jump-moment case, and each of them supplies the
  -- Laplace gap `q < X.ψ θ` without any standing assumption.
  have hgap : ∃ θ : ℝ, 0 ≤ θ ∧ q < X.ψ θ := by
    have hsplit : 0 < X.σ ∨
        (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) = ⊤ :=
      unbounded_variation_gaussian_or_infinite_small_jump_moment X hnbv
    by_cases hσpos : 0 < X.σ
    · obtain ⟨β₀, hβ, htail⟩ :=
        AvramDividend.Classical.psi_eventually_gt_of_gaussian X q hσpos
      exact ⟨β₀, hβ, htail β₀ le_rfl⟩
    · -- Without a Gaussian coefficient, unbounded variation forces the
      -- small-jump first moment to be infinite: otherwise the process
      -- would be of bounded variation.
      have hσzero : X.σ = 0 :=
        le_antisymm (le_of_not_gt hσpos) X.σ_nonneg
      have hinf : (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) = ⊤ := by
        by_contra hne
        have hlt : (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) < ⊤ :=
          lt_top_iff_ne_top.mpr hne
        exact hnbv ⟨hσzero, hlt⟩
      obtain ⟨β₀, hβ, htail⟩ :=
        AvramDividend.Classical.psi_eventually_gt_of_infinite_small_jump_moment
          X hσzero hinf q hq
      exact ⟨β₀, hβ, htail β₀ le_rfl⟩
  obtain ⟨θ, hθ, hψ⟩ := hgap
  let C : ℝ := Real.exp (θ * (x + 1)) * (X.ψ θ - q)⁻¹
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (le_of_lt (Real.exp_pos _))
      (inv_nonneg.mpr (le_of_lt (sub_pos.mpr hψ)))
  have hWnonneg : ∀ y : ℝ, 0 ≤ W y := by
    intro y
    by_cases hy : y < 0
    · rw [hW.1 y hy]
    · exact hW.2.1 y (le_of_not_gt hy)
  have hWt : Measurable W :=
    AvramDividend.Classical.chat03_scale_function_borel_measurable X q W hW
  have hXt : Measurable (X.X t) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hmeas : AEStronglyMeasurable
      (fun ω => W (x + X.X t ω)) P :=
    (hWt.comp (measurable_const.add hXt)).aestronglyMeasurable
  have hExp : Integrable (fun ω => Real.exp (θ * X.X t ω)) P :=
    (X.laplace t θ hθ).1
  have hMajorant : Integrable (fun ω => C * Real.exp (θ * X.X t ω)) P :=
    hExp.const_mul C
  apply hMajorant.mono' hmeas
  filter_upwards [] with ω
  have hb := AvramDividend.Classical.chat03_scale_global_weighted_exponential_bound
    X q W hW θ (x + X.X t ω) hθ hψ
  have hscale :
      W (x + X.X t ω) ≤
        Real.exp (θ * ((x + X.X t ω) + 1)) * (X.ψ θ - q)⁻¹ := by
    calc
      W (x + X.X t ω) =
          Real.exp (θ * ((x + X.X t ω) + 1)) *
            (Real.exp (-(θ * ((x + X.X t ω) + 1))) *
              W (x + X.X t ω)) := by
                rw [← mul_assoc, ← Real.exp_add, add_neg_cancel,
                  Real.exp_zero, one_mul]
      _ ≤ Real.exp (θ * ((x + X.X t ω) + 1)) *
          (X.ψ θ - q)⁻¹ :=
        mul_le_mul_of_nonneg_left hb (le_of_lt (Real.exp_pos _))
  have hrewrite :
      Real.exp (θ * ((x + X.X t ω) + 1)) * (X.ψ θ - q)⁻¹ =
        C * Real.exp (θ * X.X t ω) := by
    have hr : θ * ((x + X.X t ω) + 1) =
        θ * (x + 1) + θ * X.X t ω := by ring
    rw [hr, Real.exp_add]
    dsimp [C]
    ring
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hWnonneg _)] using
    hscale.trans_eq hrewrite
