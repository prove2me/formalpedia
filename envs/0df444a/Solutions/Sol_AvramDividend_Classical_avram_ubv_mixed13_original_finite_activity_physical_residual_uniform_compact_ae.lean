-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_physical_residual_uniform_compact_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T23:43:31.494927+00:00
-- url     : https://prove2.me/submissions/10ad428b-617a-4514-95a3-c050f682bda1

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

/-- Finite original jump activity makes the intrinsic compensated negative
band residual locally uniformly Cauchy, including random bounded clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ K : ℕ, ∀ η : ℝ, 0 < η →
      ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → n ≤ m →
        ∀ T : ℝ≥0, T ≤ (K : ℝ≥0) →
          |avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω -
             avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω| < η := by
  filter_upwards
      [avram_ubv_mixed13_original_finite_activity_uniform_negative_mark_void_ae
        X hFinite] with ω hω
  intro K η hη
  obtain ⟨δ, hδ, hVoid⟩ := hω (K : ℝ≥0)
  let L : ℝ := (X.ν (Iio (0 : ℝ))).toReal
  let M : ℝ := (K : ℝ) * L
  have hM : 0 ≤ M := by
    dsimp [M, L]
    exact mul_nonneg (by positivity) ENNReal.toReal_nonneg
  have hMone : 0 < M + 1 := by linarith
  have hsmall : 0 < min δ (η / (M + 1)) :=
    lt_min hδ (div_pos hη hMone)
  have hEvent : ∀ᶠ k : ℕ in atTop,
      (1 / ((k : ℝ) + 1)) < min δ (η / (M + 1)) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (isOpen_Iio.mem_nhds hsmall)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hEvent
  have hNumerical : ∀ j : ℕ, N ≤ j →
      (K : ℝ) * ((1 / ((j : ℝ) + 1)) * L) < η := by
    intro j hj
    have hjSmall : (1 / ((j : ℝ) + 1)) < η / (M + 1) :=
      lt_of_lt_of_le (hN j hj) (min_le_right _ _)
    have hjProd : (1 / ((j : ℝ) + 1)) * (M + 1) < η :=
      (lt_div_iff₀ hMone).mp hjSmall
    have hjNonneg : (0 : ℝ) ≤ 1 / ((j : ℝ) + 1) := by positivity
    have hFin : M * (1 / ((j : ℝ) + 1)) < η := by nlinarith
    calc
      (K : ℝ) * ((1 / ((j : ℝ) + 1)) * L) =
          M * (1 / ((j : ℝ) + 1)) := by dsimp [M]; ring
      _ < η := hFin
  refine ⟨N, ?_⟩
  intro n m hn hnm T hTK
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
  have hNVoidK :
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (K : ℝ≥0) ×ˢ S) = 0 :=
    hVoid S measurableSet_Ioc hS
  have hTimeSubset : Ioc (0 : ℝ≥0) T ×ˢ S ⊆
      Ioc 0 (K : ℝ≥0) ×ˢ S := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    exact ⟨⟨ht.1, le_trans ht.2 hTK⟩, hz⟩
  have hNVoidT :
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Ioc (-(1 / ((n : ℝ) + 1)))
          (-(1 / ((m : ℝ) + 1)))) = 0 := by
    exact measure_mono_null hTimeSubset hNVoidK
  have hBound :=
    avram_ubv_mixed13_original_finite_activity_void_annulus_residual_bound
      X hFinite n m hnm T ω hNVoidT
  have hTKreal : (T : ℝ) ≤ (K : ℝ) := by exact_mod_cast hTK
  calc
    |avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω -
       avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω| ≤
        (T : ℝ) * ((1 / ((n : ℝ) + 1)) * L) := hBound
    _ ≤ (K : ℝ) * ((1 / ((n : ℝ) + 1)) * L) := by
      exact mul_le_mul_of_nonneg_right hTKreal
        (mul_nonneg (by positivity) ENNReal.toReal_nonneg)
    _ < η := hNumerical n hn
