-- Prove2me | solution 2 for AvramDividend.Classical.avram_anoise37_original_dyadic_source_pathwise_convergence
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T18:49:45.683852+00:00
-- url     : https://prove2.me/submissions/2da1ac8e-283a-4873-a71d-b45d518c7a07
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_j18_original_dyadic_mark_error_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

/-- Reuse the already published exact physical source certificate. -/
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
      let J : ℕ → ℕ → Ω → ℝ≥0∞ := fun k i ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ C k i)
      let M : ℕ → Ω → ℝ := fun k ω =>
        ∑ i ∈ Finset.range (2 ^ k),
          (-1 + (i : ℝ) / (2 : ℝ) ^ k) *
            ((J k i ω).toReal -
              (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (C k i)).toReal)
      ∀ᵐ ω ∂P, Tendsto (fun k => M k ω) atTop
        (𝓝 (avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω)) := by
  intro n s t hst
  let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
  let C : ℕ → ℕ → Set ℝ := fun k i =>
    B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
      (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)
  let J : ℕ → ℕ → Ω → ℝ≥0∞ := fun k i ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ C k i)
  let M : ℕ → Ω → ℝ := fun k ω =>
    ∑ i ∈ Finset.range (2 ^ k),
      (-1 + (i : ℝ) / (2 : ℝ) ^ k) *
        ((J k i ω).toReal -
          (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (C k i)).toReal)
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 t ×ˢ Iio (0 : ℝ))
  have hRate : ∀ᵐ ω ∂P, ∀ k : ℕ,
      ‖M k ω -
        (avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω)‖ ≤
        (1 / (2 : ℝ) ^ k) *
          ((N ω).toReal +
            (t - s : ℝ≥0).toReal * (X.ν (Iio (0 : ℝ))).toReal) := by
    simpa only [B, C, J, M, N] using
      avram_j18_original_dyadic_mark_error_rate X hFinite n s t hst
  filter_upwards [hRate] with ω hω
  let target : ℝ :=
    avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω
  let K : ℝ := (N ω).toReal +
    (t - s : ℝ≥0).toReal * (X.ν (Iio (0 : ℝ))).toReal
  let e : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k * K
  have hError (k : ℕ) : |M k ω - target| ≤ e k := by
    simpa only [Real.norm_eq_abs, one_div_pow, target, e, K] using hω k
  have hpow : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have he : Tendsto e atTop (𝓝 0) := by
    simpa [e] using hpow.mul_const K
  have hlo : Tendsto (fun k => target - e k) atTop (𝓝 target) := by
    convert tendsto_const_nhds.sub he using 1 <;> simp
  have hhi : Tendsto (fun k => target + e k) atTop (𝓝 target) := by
    convert tendsto_const_nhds.add he using 1 <;> simp
  have hLim : Tendsto (fun k => M k ω) atTop (𝓝 target) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
    · intro k
      linarith [(abs_le.mp (hError k)).1]
    · intro k
      linarith [(abs_le.mp (hError k)).2]
  simpa only [M, target] using hLim