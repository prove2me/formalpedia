-- Prove2me | solution 1 for AvramDividend.Classical.nonnegative_zero_initial_martingale_vanishes_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T19:15:16.714983+00:00
-- url     : https://prove2.me/submissions/0d71c8cf-68ba-456d-b66a-8c8a2368502c

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal

/-- A nonnegative martingale with zero initial value is identically zero
almost surely at every fixed time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    [SigmaFiniteFiltration P 𝓕]
    (M : ℝ≥0 → Ω → ℝ)
    (hM : Martingale M 𝓕 P)
    (hnonneg : ∀ t : ℝ≥0, 0 ≤ᵐ[P] M t)
    (hzero : M 0 =ᵐ[P] (fun _ => (0 : ℝ))) :
    ∀ t : ℝ≥0, M t =ᵐ[P] (fun _ => (0 : ℝ)) := by
  intro t
  have hAtZero : (∫ ω : Ω, M 0 ω ∂P) = 0 := by
    rw [integral_congr_ae hzero]
    simp
  have hEq : (∫ ω : Ω, M 0 ω ∂P) =
      (∫ ω : Ω, M t ω ∂P) := by
    simpa only [setIntegral_univ] using
      (hM.setIntegral_eq (show (0 : ℝ≥0) ≤ t from bot_le)
        (s := Set.univ) (by simp))
  have hAtT : (∫ ω : Ω, M t ω ∂P) = 0 := hEq.symm.trans hAtZero
  exact (integral_eq_zero_iff_of_nonneg_ae
    (hnonneg t) (hM.integrable t)).mp hAtT
