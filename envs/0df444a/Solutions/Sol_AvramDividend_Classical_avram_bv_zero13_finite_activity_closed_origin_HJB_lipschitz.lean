-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_zero13_finite_activity_closed_origin_HJB_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T07:49:57.057957+00:00
-- url     : https://prove2.me/submissions/562bfdde-f2d8-40ab-99aa-2552cbf32945

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_finite_activity_origin_derivative_uniform_HJB
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_closed_endpoint_two_point_jump_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (ε : ℝ) (hε : 0 < ε) (hεC : ENNReal.ofReal ε < C) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ y ∈ Icc (0 : ℝ) ε, ∀ z ∈ Icc (0 : ℝ) ε,
        |w z - w y| ≤ K * |z - y| := by
  obtain ⟨K, hK, hUpper⟩ :=
    avram_bv_zero13_finite_activity_origin_derivative_uniform_HJB
      X hX hBV hFinite q hq w C hC hw_cont hw0 hw_neg
      hw_smooth hw_gen hw_grad ε hε hεC
  have hSub : Ioo (0 : ℝ) ε ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro z hz
    exact ⟨hz.1, ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hz.1.le).2 hz.2).trans hεC⟩
  have hDiff : DifferentiableOn ℝ w (interior (Icc (0 : ℝ) ε)) := by
    have hD := (hw_smooth.mono hSub).differentiableOn (by norm_num)
    exact hD.mono (by intro z hz; simpa only [interior_Icc] using hz)
  have hContG : ContinuousOn (fun t : ℝ => K * t - w t) (Icc (0 : ℝ) ε) :=
    (continuousOn_const.mul continuousOn_id).sub (hw_cont.mono (fun z hz => hz.1))
  have hConstOn : DifferentiableOn ℝ (fun _ : ℝ => K) (interior (Icc (0 : ℝ) ε)) := differentiableOn_const K
  have hIdOn : DifferentiableOn ℝ (fun t : ℝ => t) (interior (Icc (0 : ℝ) ε)) := differentiableOn_id
  have hDiffG : DifferentiableOn ℝ (fun t : ℝ => K * t - w t) (interior (Icc (0 : ℝ) ε)) :=
    (hConstOn.mul hIdOn).sub hDiff
  have hDerivG : ∀ z ∈ interior (Icc (0 : ℝ) ε), 0 ≤ deriv (fun t : ℝ => K * t - w t) z := by
    intro z hz
    have hzIoo : z ∈ Ioo (0 : ℝ) ε := by simpa only [interior_Icc] using hz
    have hwAt : DifferentiableAt ℝ w z := hDiff.differentiableAt (isOpen_interior.mem_nhds hz)
    have hD : deriv (fun t : ℝ => K * t - w t) z =
        K - deriv w z := by
      have hConstAt : DifferentiableAt ℝ (fun _ : ℝ => K) z := differentiableAt_const _
      have hIdAt : DifferentiableAt ℝ (fun t : ℝ => t) z := differentiableAt_id
      have hMulAt : DifferentiableAt ℝ (fun t : ℝ => K * t) z := hConstAt.mul hIdAt
      calc
        _ = deriv (fun t : ℝ => K * t) z - deriv w z := deriv_sub hMulAt hwAt
        _ = K - deriv w z := by simp
    rw [hD]
    have hle : deriv w z ≤ K := (le_abs_self _).trans (hUpper z hzIoo.1 hzIoo.2.le)
    linarith
  have hMono : MonotoneOn (fun t : ℝ => K * t - w t) (Icc (0 : ℝ) ε) :=
    monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) ε) hContG hDiffG hDerivG
  have hSec := avram_wave7_02_original_positive_cap_C1_closed_endpoint_two_point_jump_envelope
      C hC w hw_cont hw_smooth hw_grad ε (le_of_lt hε) hεC.le
  refine ⟨K, hK, ?_⟩; intro y hy z hz
  by_cases hyz : y ≤ z
  · have hM := hMono hy hz hyz
    have hS := hSec y hy z hz hyz
    have hw : 0 ≤ w z - w y := by linarith
    have ht : 0 ≤ z - y := by linarith
    rw [abs_of_nonneg hw, abs_of_nonneg ht]
    dsimp at hM
    nlinarith
  · have hzy : z ≤ y := le_of_not_ge hyz
    have hM := hMono hz hy hzy
    have hS := hSec z hz y hy hzy
    have hw : w z - w y ≤ 0 := by linarith
    have ht : z - y ≤ 0 := by linarith
    rw [abs_of_nonpos hw, abs_of_nonpos ht]
    dsimp at hM
    nlinarith
