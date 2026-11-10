-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf16_original_two_annulus_simple_weight_L2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T16:37:25.169208+00:00
-- url     : https://prove2.me/submissions/2ca4dde1-2f3b-4eb4-91c8-33b605a12d03

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_physical_annulus_count_variance_exact
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_original_separated_annulus_compensated_covariance_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

/-- The physical two-annulus simple test has exactly its diagonal variance. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m p q : ℕ) (hnm : n ≤ m) (hmp : m ≤ p) (hpq : p ≤ q)
    (a b : ℝ) :
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
    Integrable (fun ω => (a * Y n m ω + b * Y p q ω) ^ 2) P ∧
      (∫ ω, (a * Y n m ω + b * Y p q ω) ^ 2 ∂P) =
        a ^ 2 * r n m + b ^ 2 * r p q := by
  classical
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
  change Integrable (fun ω => (a * Y n m ω + b * Y p q ω) ^ 2) P ∧
    (∫ ω, (a * Y n m ω + b * Y p q ω) ^ 2 ∂P) =
      a ^ 2 * r n m + b ^ 2 * r p q
  have hnmVar := avram_mixed_source13_original_physical_annulus_count_variance_exact
    X T n m hnm
  change Integrable (fun ω => (Y n m ω) ^ 2) P ∧
    (∫ ω, (Y n m ω) ^ 2 ∂P) = r n m at hnmVar
  have hpqVar := avram_mixed_source13_original_physical_annulus_count_variance_exact
    X T p q hpq
  change Integrable (fun ω => (Y p q ω) ^ 2) P ∧
    (∫ ω, (Y p q ω) ^ 2 ∂P) = r p q at hpqVar
  have hcross := avram_mix_inf15_original_separated_annulus_compensated_covariance_zero
    X T n m p q hnm hmp hpq
  change Integrable (fun ω => Y n m ω * Y p q ω) P ∧
    (∫ ω, Y n m ω * Y p q ω ∂P) = 0 at hcross
  have h1 := hnmVar.1.const_mul (a ^ 2)
  have h2 := hpqVar.1.const_mul (b ^ 2)
  have h3 := hcross.1.const_mul (2 * a * b)
  have hsum := h1.add (h2.add h3)
  have hpoint (ω : Ω) :
      (a * Y n m ω + b * Y p q ω) ^ 2 =
        a ^ 2 * (Y n m ω) ^ 2 +
          (b ^ 2 * (Y p q ω) ^ 2 +
            (2 * a * b) * (Y n m ω * Y p q ω)) := by
    ring
  constructor
  · have heq :
        (fun ω => (a * Y n m ω + b * Y p q ω) ^ 2) =
          (fun ω => a ^ 2 * (Y n m ω) ^ 2 +
            (b ^ 2 * (Y p q ω) ^ 2 +
              (2 * a * b) * (Y n m ω * Y p q ω))) :=
        funext hpoint
    rw [heq]
    exact hsum
  · calc
      (∫ ω, (a * Y n m ω + b * Y p q ω) ^ 2 ∂P) =
          ∫ ω, (a ^ 2 * (Y n m ω) ^ 2 +
            (b ^ 2 * (Y p q ω) ^ 2 +
              (2 * a * b) * (Y n m ω * Y p q ω))) ∂P := by
                apply integral_congr_ae
                exact Filter.Eventually.of_forall hpoint
      _ = (∫ ω, a ^ 2 * (Y n m ω) ^ 2 ∂P) +
          (∫ ω, b ^ 2 * (Y p q ω) ^ 2 ∂P) +
          (∫ ω, (2 * a * b) * (Y n m ω * Y p q ω) ∂P) := by
        calc
          _ = (∫ ω, a ^ 2 * (Y n m ω) ^ 2 ∂P) +
              (∫ ω, b ^ 2 * (Y p q ω) ^ 2 +
                (2 * a * b) * (Y n m ω * Y p q ω) ∂P) :=
                  integral_add h1 (h2.add h3)
          _ = _ := by rw [integral_add h2 h3]; ring
      _ = a ^ 2 * r n m + b ^ 2 * r p q := by
        simp only [integral_const_mul, hnmVar.2, hpqVar.2, hcross.2]
        ring
