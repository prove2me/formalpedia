-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise32_original_smallband_signed_increment_condexp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T12:01:34.095387+00:00
-- url     : https://prove2.me/submissions/f70d5f64-9654-46c3-b2e7-ec940bfa3327

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_anoise33_original_dyadic_signed_band_L1_domination
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

/-- Dominated convergence transfers original finite-simple marked-count conditional
centring to the original signed-mark stochastic integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hInt : ∀ n : ℕ, ∀ T : ℝ≥0, Integrable
      (fun ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω) P) :
    ∀ n : ℕ, ∀ s t : ℝ≥0, s ≤ t →
      P[(fun ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω) | 𝓕.rightCont s] =ᵐ[P]
      (fun _ => (0 : ℝ)) := by
  letI : IsProbabilityMeasure P := X.isProbability
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
  obtain ⟨bound, hBoundInt, hMInt, hZero, hLim, hBound⟩ :=
    avram_anoise33_original_dyadic_signed_band_L1_domination
      X hFinite hInt n s t hst
  let f : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω
  have hEq : P[f | 𝓕.rightCont s] =ᵐ[P]
      P[(fun _ : Ω => (0 : ℝ)) | 𝓕.rightCont s] :=
    tendsto_condExp_unique M (fun _ _ => (0 : ℝ)) f (fun _ => (0 : ℝ))
      hMInt (fun _ => integrable_zero Ω ℝ P) hLim
      (Filter.Eventually.of_forall (fun _ => tendsto_const_nhds))
      bound hBoundInt (fun _ => (0 : ℝ))
      (integrable_zero Ω ℝ P) hBound
      (fun _ => Filter.Eventually.of_forall (fun _ => by simp))
      (fun k => by simpa only [M, condExp_fun_zero] using hZero k)
  simpa only [f, condExp_fun_zero] using hEq
