-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_square_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T08:49:16.537434+00:00
-- url     : https://prove2.me/submissions/32966b27-faa2-4146-8ee1-f047b398100c

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_L1_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_real_mean_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_original_band_count_factorial_moment_exact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The true negative-band count at a bounded random horizon inherits
the exact fixed-horizon second-moment budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (hKmeas : Measurable (fun ω : Ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard)) :
    let K : Ω → ℕ := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => (K ω : ℝ) ^ 2) P ∧
      (∫ ω, (K ω : ℝ) ^ 2 ∂P) ≤ r ^ 2 + r := by
  let K : Ω → ℕ := fun ω =>
    {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
  let KT : Ω → ℕ := fun ω =>
    {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
  let r : ℝ :=
    ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
  change Integrable (fun ω => (K ω : ℝ) ^ 2) P ∧
    (∫ ω, (K ω : ℝ) ^ 2 ∂P) ≤ r ^ 2 + r
  have hmeas : Measurable K := hKmeas
  have hKle (ω : Ω) : K ω ≤ KT ω := by
    apply Set.ncard_le_ncard
    · intro u hu
      exact ⟨hu.1, (hu.2.1).trans (hτ ω), hu.2.2⟩
    · exact avram_wave7_06_original_negative_band_marked_times_finite X ω T n
  have hreal (ω : Ω) : (N ω).toReal = (KT ω : ℝ) := by
    have hN : N ω = (KT ω : ℝ≥0∞) :=
      avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card X ω T n
    rw [hN, ENNReal.toReal_natCast]
  have hFirst : Integrable (fun ω => (N ω).toReal) P :=
    avram_p4_f_assembly_original_cutoff_marked_count_L1_auto X T n
  have hFirstMean : (∫ ω, (N ω).toReal ∂P) = r :=
    avram_p4_f_assembly_original_cutoff_marked_count_real_mean_auto X T n
  have hFactor := avram_p4_f2_original_band_count_factorial_moment_exact X T n
  change Integrable (fun ω => (N ω).toReal * ((N ω).toReal - 1)) P ∧
    (∫ ω, (N ω).toReal * ((N ω).toReal - 1) ∂P) = r ^ 2 at hFactor
  have hSquare : (fun ω => (KT ω : ℝ) ^ 2) =
      (fun ω => (N ω).toReal * ((N ω).toReal - 1) + (N ω).toReal) := by
    funext ω
    rw [hreal ω]
    ring
  have hFullInt : Integrable (fun ω => (KT ω : ℝ) ^ 2) P := by
    rw [hSquare]
    exact hFactor.1.add hFirst
  have hFullMean : (∫ ω, (KT ω : ℝ) ^ 2 ∂P) = r ^ 2 + r := by
    rw [hSquare, integral_add hFactor.1 hFirst, hFactor.2, hFirstMean]
  have hSquareLe (ω : Ω) : (K ω : ℝ) ^ 2 ≤ (KT ω : ℝ) ^ 2 := by
    gcongr
    exact_mod_cast hKle ω
  have hStopInt : Integrable (fun ω => (K ω : ℝ) ^ 2) P := by
    apply MeasureTheory.Integrable.mono hFullInt
      ((measurable_of_countable (fun k : ℕ => (k : ℝ) ^ 2)).comp hmeas).aestronglyMeasurable
    filter_upwards [] with ω
    change ‖(K ω : ℝ) ^ 2‖ ≤ ‖(KT ω : ℝ) ^ 2‖
    have hk0 : 0 ≤ (K ω : ℝ) ^ 2 := sq_nonneg _
    have ht0 : 0 ≤ (KT ω : ℝ) ^ 2 := sq_nonneg _
    calc
      ‖(K ω : ℝ) ^ 2‖ = (K ω : ℝ) ^ 2 := Real.norm_of_nonneg hk0
      _ ≤ (KT ω : ℝ) ^ 2 := hSquareLe ω
      _ = ‖(KT ω : ℝ) ^ 2‖ := (Real.norm_of_nonneg ht0).symm
  refine ⟨hStopInt, ?_⟩
  have hMeanLe := integral_mono_ae hStopInt hFullInt
    (Filter.Eventually.of_forall hSquareLe)
  rwa [hFullMean] at hMeanLe
