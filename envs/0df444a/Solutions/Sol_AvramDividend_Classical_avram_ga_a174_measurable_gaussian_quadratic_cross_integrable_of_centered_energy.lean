-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a174_measurable_gaussian_quadratic_cross_integrable_of_centered_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:43:03.416173+00:00
-- url     : https://prove2.me/submissions/ea0738df-771b-4500-95e1-6b1ba6070bca

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a175_finite_mask_gaussian_raw_centered_square_cross_domination
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

/-- Expected absolute raw-centred Gaussian cross is integrable whenever its
original finite source centred quadratic energy is integrable. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (S : Finset ℕ) (A : ℕ → Ω → Prop)
    [∀ i, DecidablePred (A i)]
    (hA : ∀ i, MeasurableSet {ω | A i ω})
    (Z : ℕ → Ω → ℝ) (hZ : ∀ i, Measurable (Z i))
    (d : ℝ)
    (hEI : Integrable (fun ω =>
      ∑ i ∈ S, if A i ω then (Z i ω)^2 else 0) P) :
    Integrable (fun ω =>
      ∑ i ∈ S, if A i ω then
        |(Z i ω + d)^2 - (Z i ω)^2| else 0) P := by
  classical
  let F : Ω → ℝ := fun ω =>
    ∑ i ∈ S, if A i ω then
      |(Z i ω + d)^2 - (Z i ω)^2| else 0
  let E : Ω → ℝ := fun ω =>
    ∑ i ∈ S, if A i ω then (Z i ω)^2 else 0
  have hm : Measurable F := by
    dsimp [F]
    apply Finset.measurable_sum
    intro i hi
    exact Measurable.ite (hA i) (by fun_prop (disch := exact hZ i)) measurable_const
  have hp (ω : Ω) : 0 ≤ F ω := by
    dsimp [F]
    apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> positivity
  have hb (ω : Ω) : F ω ≤ E ω + (S.card : ℝ) * (2 * d^2) :=
    avram_ga_a175_finite_mask_gaussian_raw_centered_square_cross_domination
      S A Z d ω
  have hDom : Integrable
      (fun ω => E ω + (S.card : ℝ) * (2 * d^2)) P :=
    hEI.add (integrable_const _)
  apply hDom.mono' hm.aestronglyMeasurable
  filter_upwards [] with ω
  have he : 0 ≤ E ω := by
    dsimp [E]
    apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> positivity
  have hCard : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have hCorrection : 0 ≤ (S.card : ℝ) * (2 * d^2) :=
    mul_nonneg hCard (mul_nonneg (by norm_num) (sq_nonneg _))
  have hd : 0 ≤ E ω + (S.card : ℝ) * (2 * d^2) :=
    add_nonneg he hCorrection
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hp ω), abs_of_nonneg hd] using hb ω
