-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_factorial_highcount_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:38:36.816437+00:00
-- url     : https://prove2.me/submissions/ca102066-c978-4423-973b-9335197ebddf

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_factorial_pair_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original bounded stopped negative-band high counts have exact factorial
    second-physical-order probability tails. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (hKmeas : Measurable (fun ω : Ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard))
    (m : ℕ) (hm : 2 ≤ m) :
    let K : Ω → ℕ := fun ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    P.real {ω : Ω | m ≤ K ω} ≤
      r ^ 2 / ((m : ℝ) * ((m : ℝ) - 1)) := by
  let K : Ω → ℕ := fun ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
  let r : ℝ :=
    ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
  let d : ℝ := (m : ℝ) * ((m : ℝ) - 1)
  change P.real {ω : Ω | m ≤ K ω} ≤ r ^ 2 / d
  have hmreal : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hdpos : 0 < d := by
    dsimp [d]
    exact mul_pos (by linarith) (by linarith)
  have hFact :=
    avram_p4_s3_original_bounded_stop_negative_band_factorial_pair_moment
      X T n τ hτ hKmeas
  change Integrable (fun ω => (K ω : ℝ) * ((K ω : ℝ) - 1)) P ∧
    (∫ ω, (K ω : ℝ) * ((K ω : ℝ) - 1) ∂P) ≤ r ^ 2 at hFact
  have hKmeas' : Measurable K := hKmeas
  have hEvent : MeasurableSet {ω : Ω | m ≤ K ω} := by
    change MeasurableSet (K ⁻¹' Ici m)
    exact hKmeas' measurableSet_Ici
  have hPointwise (k : ℕ) :
      d * (if m ≤ k then (1 : ℝ) else 0) ≤
      (k : ℝ) * ((k : ℝ) - 1) := by
    by_cases hk : m ≤ k
    · simp only [if_pos hk, mul_one]
      have hkreal : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hDiff : 0 ≤ ((k : ℝ) - m) *
          ((k : ℝ) + m - 1) :=
        mul_nonneg (by linarith) (by linarith)
      dsimp [d]
      nlinarith
    · simp only [if_neg hk, mul_zero]
      cases k with
      | zero => norm_num
      | succ j =>
        have hj : (1 : ℝ) ≤ (Nat.succ j : ℝ) := by
          exact_mod_cast (show 1 ≤ Nat.succ j by omega)
        exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hj)
  have hIf :
      (fun ω : Ω => if m ≤ K ω then (1 : ℝ) else 0) =
      ({ω : Ω | m ≤ K ω}).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases hk : m ≤ K ω <;> simp [Set.indicator, hk]
  have hIfInt : Integrable
      (fun ω : Ω => if m ≤ K ω then (1 : ℝ) else 0) P := by
    rw [hIf]
    exact (integrable_const (1 : ℝ)).indicator hEvent
  have hIfMean :
      (∫ ω, (if m ≤ K ω then (1 : ℝ) else 0) ∂P) =
        P.real {ω : Ω | m ≤ K ω} := by
    rw [hIf]
    exact integral_indicator_one hEvent
  have hBound := integral_mono_ae (hIfInt.const_mul d) hFact.1
    (Filter.Eventually.of_forall (fun ω => hPointwise (K ω)))
  rw [integral_const_mul, hIfMean] at hBound
  apply (le_div_iff₀ hdpos).2
  calc
    P.real {ω : Ω | m ≤ K ω} * d =
        d * P.real {ω : Ω | m ≤ K ω} := mul_comm _ _
    _ ≤ r ^ 2 := hBound.trans hFact.2
