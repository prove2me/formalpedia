-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_02b_actual_source_weighted_cell_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:52:43.928722+00:00
-- url     : https://prove2.me/submissions/1e4e828d-551c-45cc-9f1b-6577fbf25a38

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_actual_levy_past_indep_measurable_future_jump_family_ws01b

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (C : Set ℝ) (f : ℝ → ℝ) (ν : Measure ℝ) (rate : ℝ)
    (H : Ω → ℝ) (hH : Measurable[𝓕 s] H)
    (hH2 : Integrable (fun ω => H ω ^ 2) P)
    (J : (ℝ≥0 → ℝ) → ℝ) (hJ : Measurable J)
    (hRep : ∀ ω, J (fun t : ℝ≥0 =>
      X.X (s + t) ω - X.X s ω) =
      (∫ p in Set.Ioc s (s + T) ×ˢ C, f p.2 ∂(NX ω)) -
        rate * ∫ z, f z ∂ν)
    (hJ2int : Integrable
      (fun ω => (J (fun t => X.X (s + t) ω - X.X s ω)) ^ 2) P)
    (hSecond : (∫ ω, (J (fun t => X.X (s + t) ω - X.X s ω)) ^ 2 ∂P) =
      rate * ∫ z, f z ^ 2 ∂ν) :
    let Z : Ω → ℝ := fun ω =>
      (∫ p in Set.Ioc s (s + T) ×ˢ C, f p.2 ∂(NX ω)) -
        rate * ∫ z, f z ∂ν
    Integrable (fun ω => (H ω * Z ω) ^ 2) P ∧
      (∫ ω, (H ω * Z ω) ^ 2 ∂P) =
        (∫ ω, H ω ^ 2 ∂P) * (rate * ∫ z, f z ^ 2 ∂ν) := by
  have hi := actual_levy_past_indep_measurable_future_jump_family_ws01b
    X s (fun ω => H ω ^ 2) (hH.pow_const 2)
    (fun x => J x ^ 2) (hJ.pow_const 2)
  have hint := hi.integrable_mul hH2 hJ2int
  have heq := hi.integral_mul_eq_mul_integral
    hH2.aestronglyMeasurable hJ2int.aestronglyMeasurable
  change Integrable (fun ω => H ω ^ 2 *
    (J (fun t => X.X (s + t) ω - X.X s ω)) ^ 2) P at hint
  change (∫ ω, H ω ^ 2 *
    (J (fun t => X.X (s + t) ω - X.X s ω)) ^ 2 ∂P) =
      (∫ ω, H ω ^ 2 ∂P) *
        (∫ ω, (J (fun t => X.X (s + t) ω - X.X s ω)) ^ 2 ∂P) at heq
  rw [hSecond] at heq
  simp_rw [hRep] at hint heq
  dsimp only
  constructor
  · simpa only [mul_pow] using hint
  · simpa only [mul_pow] using heq
