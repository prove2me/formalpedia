-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise42_original_dyadic_levy_compensator_approx
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T14:36:54.317724+00:00
-- url     : https://prove2.me/submissions/675d3948-3246-4e8e-a490-344cd9f9ecea

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_anoise44_dyadic_levy_signed_integral_quadrature_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

/-- Quantitative original Lévy quadrature error yields compensated-rate convergence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hInt : ∀ n : ℕ, ∀ T : ℝ≥0, Integrable
      (fun ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω) P) :
    ∀ n : ℕ, ∀ s t : ℝ≥0, s ≤ t →
      let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
      let C : ℕ → ℕ → Set ℝ := fun k i =>
        B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
          (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)
      Tendsto
        (fun k => ∑ i ∈ Finset.range (2 ^ k),
          (-1 + (i : ℝ) / (2 : ℝ) ^ k) *
            ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (C k i)).toReal))
        atTop
        (𝓝 (((t - s : ℝ≥0) : ℝ) * (∫ z in B, z ∂X.ν))) := by
  intro n s t hst
  let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
  let C : ℕ → ℕ → Set ℝ := fun k i =>
    B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k) (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)
  let I : ℝ := ∫ z in B, z ∂X.ν
  let q : ℕ → ℝ := fun k => ∑ i ∈ Finset.range (2 ^ k),
    (-1 + (i : ℝ) / (2 : ℝ) ^ k) * (X.ν (C k i)).toReal
  let e : ℕ → ℝ := fun k => (1 / (2 : ℝ) ^ k) * (X.ν B).toReal
  have hq (k : ℕ) : |q k - I| ≤ e k := by
    simpa only [q, I, e, B, C] using
      avram_anoise44_dyadic_levy_signed_integral_quadrature_bound X hFinite n k
  have hpow : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have he : Tendsto e atTop (𝓝 0) := by
    have hh := hpow.mul_const (X.ν B).toReal
    convert hh using 1
    · funext k
      dsimp [e]
      rw [one_div_pow]
    · simp
  have hqLim : Tendsto q atTop (𝓝 I) := by
    have hlo : Tendsto (fun k => I - e k) atTop (𝓝 I) := by
      convert tendsto_const_nhds.sub he using 1 <;> simp
    have hhi : Tendsto (fun k => I + e k) atTop (𝓝 I) := by
      convert tendsto_const_nhds.add he using 1 <;> simp
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
    · intro k; linarith [(abs_le.mp (hq k)).1]
    · intro k; linarith [(abs_le.mp (hq k)).2]
  have hrate (k : ℕ) :
      (∑ i ∈ Finset.range (2 ^ k),
        (-1 + (i : ℝ) / (2 : ℝ) ^ k) *
          ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (C k i)).toReal)) =
      ((t - s : ℝ≥0) : ℝ) * q k := by
    dsimp [q]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ENNReal.toReal_mul]
    have hdt : ((((t - s : ℝ≥0) : ℝ≥0∞)).toReal) =
        ((t - s : ℝ≥0) : ℝ) := rfl
    rw [hdt]
    ring
  convert hqLim.const_mul (((t - s : ℝ≥0) : ℝ)) using 1
  · funext k
    exact hrate k
