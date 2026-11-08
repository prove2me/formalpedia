-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussian12_finite_gaussian_stopped_cells_positive_mask
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:36:29.448148+00:00
-- url     : https://prove2.me/submissions/587d935d-8c1a-42a6-b5af-5c2640f09966

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_avram_gaussian12_stopped_condexp_to_positive_clock_mask
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτstop : ∀ i ∈ S, IsStoppingTime 𝓕.rightCont
      (fun ω => (τ i ω : WithTop ℝ≥0)))
    (M : ι → Ω → ℝ)
    (hMI : ∀ i ∈ S, Integrable (M i) P)
    (hStoppedZero : ∀ i (hi : i ∈ S),
      condExp (hτstop i hi).measurableSpace P (M i) =ᵐ[P]
        (fun _ => (0 : ℝ))) :
    (∫ ω in {ω : Ω | σ ω ≠ 0}, ∑ i ∈ S, M i ω ∂P) = 0 := by
  rw [integral_finset_sum S (by
    intro i hi
    exact (hMI i hi).integrableOn)]
  apply Finset.sum_eq_zero
  intro i hi
  exact
    AvramDividend.Classical.avram_gaussian12_stopped_condexp_to_positive_clock_mask
      σ (τ i) hσstop (hτstop i hi) (M i) (hMI i hi)
      (hStoppedZero i hi)
