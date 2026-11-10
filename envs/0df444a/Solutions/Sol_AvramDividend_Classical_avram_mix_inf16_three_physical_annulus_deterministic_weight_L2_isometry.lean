-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf16_three_physical_annulus_deterministic_weight_L2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T16:54:00.225193+00:00
-- url     : https://prove2.me/submissions/13da6cb1-21a9-425c-b7d2-bf0ae3ea2406

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf16_original_two_annulus_simple_weight_L2_isometry
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_physical_annulus_count_variance_exact
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_original_separated_annulus_compensated_covariance_zero
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_original_adjacent_annulus_compensated_covariance_zero
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_physical_annulus_count_variance_exact
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_original_adjacent_annulus_compensated_covariance_zero
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_original_separated_annulus_compensated_covariance_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m p q : ℕ) (hnm : n ≤ m) (hmp : m ≤ p) (hpq : p ≤ q)
    (a b c : ℝ) :
    let B : ℕ → ℕ → Set ℝ := fun i j =>
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((j : ℝ) + 1)))
    let N : ℕ → ℕ → Ω → ℝ≥0∞ := fun i j ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B i j)
    let r : ℕ → ℕ → ℝ := fun i j =>
      ((T : ℝ≥0∞) * X.ν (B i j)).toReal
    let Y : ℕ → ℕ → Ω → ℝ := fun i j ω =>
      (N i j ω).toReal - r i j
    Integrable (fun ω =>
      (a * Y n m ω + b * Y m p ω + c * Y p q ω) ^ 2) P ∧
    (∫ ω, (a * Y n m ω + b * Y m p ω + c * Y p q ω) ^ 2 ∂P) =
      a ^ 2 * r n m + b ^ 2 * r m p + c ^ 2 * r p q := by
  let B : ℕ → ℕ → Set ℝ := fun i j =>
    Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((j : ℝ) + 1)))
  let N : ℕ → ℕ → Ω → ℝ≥0∞ := fun i j ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B i j)
  let r : ℕ → ℕ → ℝ := fun i j =>
    ((T : ℝ≥0∞) * X.ν (B i j)).toReal
  let Y : ℕ → ℕ → Ω → ℝ := fun i j ω => (N i j ω).toReal - r i j
  let E : Ω → ℝ := fun ω => a * Y n m ω + b * Y m p ω
  change Integrable (fun ω => (E ω + c * Y p q ω) ^ 2) P ∧
    (∫ ω, (E ω + c * Y p q ω) ^ 2 ∂P) =
      a ^ 2 * r n m + b ^ 2 * r m p + c ^ 2 * r p q
  have he : Integrable (fun ω => (E ω) ^ 2) P ∧
      (∫ ω, (E ω) ^ 2 ∂P) =
        a ^ 2 * r n m + b ^ 2 * r m p :=
    avram_mix_inf16_original_two_annulus_simple_weight_L2_isometry
      X T n m m p hnm (le_refl m) hmp a b
  have hz : Integrable (fun ω => (Y p q ω) ^ 2) P ∧
      (∫ ω, (Y p q ω) ^ 2 ∂P) = r p q :=
    avram_mixed_source13_original_physical_annulus_count_variance_exact
      X T p q hpq
  have hc1 : Integrable (fun ω => Y n m ω * Y p q ω) P ∧
      (∫ ω, Y n m ω * Y p q ω ∂P) = 0 :=
    avram_mix_inf15_original_separated_annulus_compensated_covariance_zero
      X T n m p q hnm hmp hpq
  have hc2 : Integrable (fun ω => Y m p ω * Y p q ω) P ∧
      (∫ ω, Y m p ω * Y p q ω ∂P) = 0 :=
    avram_mix_inf15_original_adjacent_annulus_compensated_covariance_zero
      X T m p q hmp hpq
  have hcrossfun :
      (fun ω => E ω * Y p q ω) =
        (fun ω => a * (Y n m ω * Y p q ω) +
          b * (Y m p ω * Y p q ω)) := by
    funext ω
    dsimp [E]
    ring
  have hcross : Integrable (fun ω => E ω * Y p q ω) P := by
    rw [hcrossfun]
    exact (hc1.1.const_mul _).add (hc2.1.const_mul _)
  have hcrosszero : (∫ ω, E ω * Y p q ω ∂P) = 0 := by
    rw [hcrossfun]
    rw [integral_add (hc1.1.const_mul _) (hc2.1.const_mul _)]
    simp only [integral_const_mul, hc1.2, hc2.2, mul_zero, add_zero]
  have hpow :
      (fun ω => (E ω + c * Y p q ω) ^ 2) =
        (fun ω => (E ω) ^ 2 +
          (c ^ 2 * (Y p q ω) ^ 2 +
            (2 * c) * (E ω * Y p q ω))) := by
    funext ω
    ring
  have hfirst : Integrable (fun ω => (E ω) ^ 2) P := he.1
  have hsecond : Integrable (fun ω => c ^ 2 * (Y p q ω) ^ 2) P :=
    hz.1.const_mul _
  have hthird : Integrable (fun ω => (2 * c) * (E ω * Y p q ω)) P :=
    hcross.const_mul _
  constructor
  · rw [hpow]
    exact hfirst.add (hsecond.add hthird)
  · rw [hpow]
    calc
      (∫ ω, (E ω) ^ 2 +
          (c ^ 2 * (Y p q ω) ^ 2 +
            (2 * c) * (E ω * Y p q ω)) ∂P) =
        (∫ ω, (E ω) ^ 2 ∂P) +
          (∫ ω, c ^ 2 * (Y p q ω) ^ 2 +
            (2 * c) * (E ω * Y p q ω) ∂P) := by
              exact integral_add hfirst (hsecond.add hthird)
      _ = (∫ ω, (E ω) ^ 2 ∂P) +
          (c ^ 2 * (∫ ω, (Y p q ω) ^ 2 ∂P) +
            (2 * c) * (∫ ω, E ω * Y p q ω ∂P)) := by
              rw [integral_add hsecond hthird]
              simp only [integral_const_mul]
      _ = a ^ 2 * r n m + b ^ 2 * r m p + c ^ 2 * r p q := by
        rw [he.2, hz.2, hcrosszero]
        ring
