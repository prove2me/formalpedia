-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_factorial_pair_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:17:28.27783+00:00
-- url     : https://prove2.me/submissions/4d9855e7-2101-42fa-b27c-9157e7be9876

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_original_band_count_factorial_moment_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact original stopped physical finite-band factorial pair count
    inherits the deterministic second factorial moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (hKmeas : Measurable (fun ω : Ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard)) :
    let K : Ω → ℕ := fun ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => (K ω : ℝ) * ((K ω : ℝ) - 1)) P ∧
    (∫ ω, (K ω : ℝ) * ((K ω : ℝ) - 1) ∂P) ≤ r ^ 2 := by
  classical
  let K : Ω → ℕ := fun ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
  let KT : Ω → ℕ := fun ω => {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
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
  change Integrable (fun ω => (K ω : ℝ) * ((K ω : ℝ) - 1)) P ∧
    (∫ ω, (K ω : ℝ) * ((K ω : ℝ) - 1) ∂P) ≤ r ^ 2
  have hKle (ω : Ω) : K ω ≤ KT ω := by
    apply Set.ncard_le_ncard
    · intro u hu
      exact ⟨hu.1, (hu.2.1).trans (hτ ω), hu.2.2⟩
    · exact avram_wave7_06_original_negative_band_marked_times_finite X ω T n
  have hReal (ω : Ω) : (N ω).toReal = (KT ω : ℝ) := by
    have hN : N ω = (KT ω : ℝ≥0∞) :=
      avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card X ω T n
    rw [hN, ENNReal.toReal_natCast]
  have hFixed := avram_p4_f2_original_band_count_factorial_moment_exact X T n
  change Integrable (fun ω => (N ω).toReal * ((N ω).toReal - 1)) P ∧
    (∫ ω, (N ω).toReal * ((N ω).toReal - 1) ∂P) = r ^ 2 at hFixed
  have hFun : (fun ω => (N ω).toReal * ((N ω).toReal - 1)) =
      (fun ω => (KT ω : ℝ) * ((KT ω : ℝ) - 1)) := by
    funext ω
    rw [hReal ω]
  rw [hFun] at hFixed
  have hKmeas' : Measurable K := hKmeas
  have hKmeasR : Measurable
      (fun ω => (K ω : ℝ) * ((K ω : ℝ) - 1)) :=
    (measurable_of_countable
      (fun k : ℕ => (k : ℝ) * ((k : ℝ) - 1))).comp hKmeas'
  have hNonneg (k : ℕ) : 0 ≤ (k : ℝ) * ((k : ℝ) - 1) := by
    cases k with
    | zero => norm_num
    | succ j =>
      have hj : (1 : ℝ) ≤ (Nat.succ j : ℝ) := by
        exact_mod_cast (show 1 ≤ Nat.succ j by omega)
      exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hj)
  have hMono (ω : Ω) :
      (K ω : ℝ) * ((K ω : ℝ) - 1) ≤
        (KT ω : ℝ) * ((KT ω : ℝ) - 1) := by
    by_cases hTzero : KT ω = 0
    · have hSmall : K ω ≤ KT ω := hKle ω
      have hKzero : K ω = 0 := by omega
      simp [hTzero, hKzero]
    · have hTge : (1 : ℝ) ≤ (KT ω : ℝ) := by
        exact_mod_cast (show 1 ≤ KT ω by omega)
      have hKge : (0 : ℝ) ≤ K ω := Nat.cast_nonneg _
      have hLe : (K ω : ℝ) ≤ KT ω := by exact_mod_cast hKle ω
      have hPos : 0 ≤ ((KT ω : ℝ) - K ω) *
          ((KT ω : ℝ) + K ω - 1) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
  have hI : Integrable (fun ω => (K ω : ℝ) * ((K ω : ℝ) - 1)) P := by
    apply Integrable.mono hFixed.1 hKmeasR.aestronglyMeasurable
    filter_upwards [] with ω
    change ‖(K ω : ℝ) * ((K ω : ℝ) - 1)‖ ≤
      ‖(KT ω : ℝ) * ((KT ω : ℝ) - 1)‖
    rw [Real.norm_of_nonneg (hNonneg (K ω)),
      Real.norm_of_nonneg (hNonneg (KT ω))]
    exact hMono ω
  refine ⟨hI, ?_⟩
  have hBound := integral_mono_ae hI hFixed.1
    (Filter.Eventually.of_forall hMono)
  rwa [hFixed.2] at hBound

