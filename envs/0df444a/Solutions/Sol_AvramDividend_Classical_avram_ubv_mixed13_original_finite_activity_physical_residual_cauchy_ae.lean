-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_physical_residual_cauchy_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T23:42:36.075759+00:00
-- url     : https://prove2.me/submissions/dedd420e-9370-47f9-82d0-b5cad65a8ab2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_uniform_negative_mark_void_ae
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_void_annulus_residual_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical Filter
open scoped NNReal ENNReal
noncomputable section

/-- On every physical finite horizon the original finite-activity
compensated small-negative-band residual is pathwise Cauchy almost surely. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      CauchySeq (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k T ω) := by
  filter_upwards
      [avram_ubv_mixed13_original_finite_activity_uniform_negative_mark_void_ae
        X hFinite] with ω hω
  intro T
  obtain ⟨δ, hδ, hVoid⟩ := hω T
  let L : ℝ := (X.ν (Iio (0 : ℝ))).toReal
  let M : ℝ := (T : ℝ) * L
  have hM : 0 ≤ M := by
    dsimp [M, L]
    exact mul_nonneg (by positivity) ENNReal.toReal_nonneg
  apply Metric.cauchySeq_iff.mpr
  intro η hη
  have hMone : 0 < M + 1 := by linarith
  have hsmall : 0 < min δ (η / (M + 1)) :=
    lt_min hδ (div_pos hη hMone)
  have hEvent : ∀ᶠ k : ℕ in atTop,
      (1 / ((k : ℝ) + 1)) < min δ (η / (M + 1)) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (isOpen_Iio.mem_nhds hsmall)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hEvent
  have hBand : ∀ n m : ℕ, N ≤ n → n ≤ m →
      |avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω -
         avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω| ≤
        (T : ℝ) * ((1 / ((n : ℝ) + 1)) * L) := by
    intro n m hn hnm
    let S : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1)))
      (-(1 / ((m : ℝ) + 1)))
    have hδn : (1 / ((n : ℝ) + 1)) < δ :=
      lt_of_lt_of_le (hN n hn) (min_le_left _ _)
    have hS : S ⊆ Ioo (-δ) 0 := by
      intro z hz
      have hm : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      change -(1 / ((n : ℝ) + 1)) < z ∧
        z ≤ -(1 / ((m : ℝ) + 1)) at hz
      constructor <;> linarith
    have hNVoid :
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ Ioc (-(1 / ((n : ℝ) + 1)))
            (-(1 / ((m : ℝ) + 1)))) = 0 := by
      exact hVoid S measurableSet_Ioc hS
    exact avram_ubv_mixed13_original_finite_activity_void_annulus_residual_bound
      X hFinite n m hnm T ω hNVoid
  have hNumerical : ∀ j : ℕ, N ≤ j →
      (T : ℝ) * ((1 / ((j : ℝ) + 1)) * L) < η := by
    intro j hj
    have hjSmall : (1 / ((j : ℝ) + 1)) < η / (M + 1) :=
      lt_of_lt_of_le (hN j hj) (min_le_right _ _)
    have hjProd : (1 / ((j : ℝ) + 1)) * (M + 1) < η :=
      (lt_div_iff₀ hMone).mp hjSmall
    have hjNonneg : (0 : ℝ) ≤ 1 / ((j : ℝ) + 1) := by positivity
    have hFin : M * (1 / ((j : ℝ) + 1)) < η := by nlinarith
    calc
      (T : ℝ) * ((1 / ((j : ℝ) + 1)) * L) =
          M * (1 / ((j : ℝ) + 1)) := by dsimp [M]; ring
      _ < η := hFin
  refine ⟨N, ?_⟩
  intro m hm n hn
  rcases le_total m n with hmn | hnm
  · rw [Real.dist_eq, abs_sub_comm]
    exact lt_of_le_of_lt (hBand m n hm hmn) (hNumerical m hm)
  · rw [Real.dist_eq]
    exact lt_of_le_of_lt (hBand n m hn hnm) (hNumerical n hn)
