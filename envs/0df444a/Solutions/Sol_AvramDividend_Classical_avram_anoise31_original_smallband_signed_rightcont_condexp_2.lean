-- Prove2me | solution 2 for AvramDividend.Classical.avram_anoise31_original_smallband_signed_rightcont_condexp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T17:59:12.803193+00:00
-- url     : https://prove2.me/submissions/1cbb81ed-10ef-4f20-8af2-25b397c0e77c

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_anoise32_original_smallband_future_increment_condexp_zero
import Theorems.Thm_AvramDividend_Classical_avram_anoise33_original_smallband_compensator_adapted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Source-faithful reduction: a centred future increment plus original adaptedness gives a martingale. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hInt : ∀ n : ℕ, ∀ T : ℝ≥0, Integrable
      (fun ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω) P) :
    ∀ n : ℕ, ∀ s t : ℝ≥0, s ≤ t → ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont s) P
        (fun ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) ω =
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro n s t hst
  let J : ℝ≥0 → Ω → ℝ :=
    fun u ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X n u ω
  have hMeas : Measurable[𝓕.rightCont s] (J s) := by
    exact (avram_anoise33_original_smallband_compensator_adapted X n s).mono
      ((Filtration.le_rightCont 𝓕) s) le_rfl
  have hPast : condExp (𝓕.rightCont s) P (J s) = J s :=
    condExp_of_stronglyMeasurable (𝓕.rightCont.le s)
      hMeas.stronglyMeasurable (hInt n s)
  have hZero :
      condExp (𝓕.rightCont s) P (fun ω => J t ω - J s ω)
        =ᵐ[P] (fun _ => 0) :=
    avram_anoise32_original_smallband_future_increment_condexp_zero
      X hFinite hInt n s t hst
  have hSub := condExp_sub (hInt n t) (hInt n s) (𝓕.rightCont s)
  filter_upwards [hZero, hSub] with ω hz hs
  change condExp (𝓕.rightCont s) P (J t) ω = J s ω
  have hDiff :
      condExp (𝓕.rightCont s) P (J t) ω -
        condExp (𝓕.rightCont s) P (J s) ω = 0 := by
    calc
      _ = condExp (𝓕.rightCont s) P (fun u => J t u - J s u) ω := hs.symm
      _ = 0 := hz
  rw [hPast] at hDiff
  exact sub_eq_zero.mp hDiff
