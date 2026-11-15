-- Prove2me | solution 1 for AvramDividend.Classical.avram_b246_original_ruinclipped_true_physical_marked_cell_uniform_second_moment_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:42:41.611563+00:00
-- url     : https://prove2.me/submissions/89d5c118-7c22-4180-993b-dcea9bb66b59

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b244_original_true_stopping_clock_ruinclipped_marked_cell_L1_dom_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_exact_raw_second_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n m : ℕ) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0)) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let grid : Ω → ℕ → ℝ≥0 := fun ω i =>
      min ((i : ℝ≥0) * Δ) (σ ω)
    let marked : Ω → Finset ℕ := fun ω => by
      classical
      exact (Finset.range (m + 1)).filter (fun i =>
        ∃ u : ℝ≥0, grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
          X.X u ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) u ≠ 0)
    let rate : ℝ :=
      ((n : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal
    Integrable (fun ω => ((marked ω).card : ℝ) ^ 2) P ∧
      (∫ ω, ((marked ω).card : ℝ) ^ 2 ∂P) ≤ rate ^ 2 + rate := by
  intro Δ grid marked rate
  obtain ⟨hMeas, hInt, hBound⟩ :=
    avram_b244_original_true_stopping_clock_ruinclipped_marked_cell_L1_dom_20261114
      X hFinite n m σ hσstop hσbound
  obtain ⟨hNInt, hNMean⟩ :=
    avram_a20_original_negative_borel_exact_raw_second_moment
      X hFinite (n : ℝ≥0) (Iio (0 : ℝ))
      measurableSet_Iio (Set.Subset.rfl)
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun t : ℝ≥0 => X.X t ω) u)))
      (Ioc 0 (n : ℝ≥0) ×ˢ Iio (0 : ℝ))
  have hSquareBound : ∀ᵐ ω ∂P,
      ((marked ω).card : ℝ) ^ 2 ≤ ((N ω).toReal) ^ 2 := by
    filter_upwards [hBound] with ω hω
    apply (sq_le_sq).2
    rw [abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg ENNReal.toReal_nonneg]
    exact hω
  have hSqMeas : AEStronglyMeasurable
      (fun ω => ((marked ω).card : ℝ) ^ 2) P :=
    (hMeas.pow_const 2).aestronglyMeasurable
  have hSqInt : Integrable (fun ω => ((marked ω).card : ℝ) ^ 2) P :=
    hNInt.mono hSqMeas (by
      filter_upwards [hSquareBound] with ω hw
      have ha : 0 ≤ ((marked ω).card : ℝ) ^ 2 := sq_nonneg _
      have hb : 0 ≤ ((N ω).toReal) ^ 2 := sq_nonneg _
      change |((marked ω).card : ℝ) ^ 2| ≤ |((N ω).toReal) ^ 2|
      rw [abs_of_nonneg ha, abs_of_nonneg hb]
      exact hw)
  refine ⟨hSqInt, ?_⟩
  calc
    (∫ ω, ((marked ω).card : ℝ) ^ 2 ∂P) ≤
        (∫ ω, ((N ω).toReal) ^ 2 ∂P) :=
      integral_mono_ae hSqInt hNInt hSquareBound
    _ = rate ^ 2 + rate := hNMean
