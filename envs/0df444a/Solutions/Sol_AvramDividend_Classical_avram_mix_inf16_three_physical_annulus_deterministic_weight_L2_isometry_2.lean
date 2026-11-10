-- Prove2me | solution 2 for AvramDividend.Classical.avram_mix_inf16_three_physical_annulus_deterministic_weight_L2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T16:55:29.619579+00:00
-- url     : https://prove2.me/submissions/0c69e134-31b3-4340-b832-95953cfccd9a

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_physical_annulus_count_variance_exact
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_original_adjacent_annulus_compensated_covariance_zero
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_original_separated_annulus_compensated_covariance_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

/-- Exact L² isometry for deterministic weights on three disjoint physical mark annuli. -/
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
  let Y : ℕ → ℕ → Ω → ℝ := fun i j ω =>
    (N i j ω).toReal - r i j
  let V1 : Ω → ℝ := Y n m
  let V2 : Ω → ℝ := Y m p
  let V3 : Ω → ℝ := Y p q
  change Integrable (fun ω => (a * V1 ω + b * V2 ω + c * V3 ω) ^ 2) P ∧
    (∫ ω, (a * V1 ω + b * V2 ω + c * V3 ω) ^ 2 ∂P) =
      a ^ 2 * r n m + b ^ 2 * r m p + c ^ 2 * r p q
  have hV1 := avram_mixed_source13_original_physical_annulus_count_variance_exact X T n m hnm
  have hV2 := avram_mixed_source13_original_physical_annulus_count_variance_exact X T m p hmp
  have hV3 := avram_mixed_source13_original_physical_annulus_count_variance_exact X T p q hpq
  change Integrable (fun ω => (V1 ω) ^ 2) P ∧ (∫ ω, (V1 ω) ^ 2 ∂P) = r n m at hV1
  change Integrable (fun ω => (V2 ω) ^ 2) P ∧ (∫ ω, (V2 ω) ^ 2 ∂P) = r m p at hV2
  change Integrable (fun ω => (V3 ω) ^ 2) P ∧ (∫ ω, (V3 ω) ^ 2 ∂P) = r p q at hV3
  have hC12 := avram_mix_inf15_original_adjacent_annulus_compensated_covariance_zero
    X T n m p hnm hmp
  have hC23 := avram_mix_inf15_original_adjacent_annulus_compensated_covariance_zero
    X T m p q hmp hpq
  have hC13 := avram_mix_inf15_original_separated_annulus_compensated_covariance_zero
    X T n m p q hnm hmp hpq
  change Integrable (fun ω => V1 ω * V2 ω) P ∧ (∫ ω, V1 ω * V2 ω ∂P) = 0 at hC12
  change Integrable (fun ω => V2 ω * V3 ω) P ∧ (∫ ω, V2 ω * V3 ω ∂P) = 0 at hC23
  change Integrable (fun ω => V1 ω * V3 ω) P ∧ (∫ ω, V1 ω * V3 ω ∂P) = 0 at hC13
  let K1 : Ω → ℝ := fun ω => a ^ 2 * (V1 ω) ^ 2
  let K2 : Ω → ℝ := fun ω => b ^ 2 * (V2 ω) ^ 2
  let K3 : Ω → ℝ := fun ω => c ^ 2 * (V3 ω) ^ 2
  let K4 : Ω → ℝ := fun ω => (2 * a * b) * (V1 ω * V2 ω)
  let K5 : Ω → ℝ := fun ω => (2 * a * c) * (V1 ω * V3 ω)
  let K6 : Ω → ℝ := fun ω => (2 * b * c) * (V2 ω * V3 ω)
  have hI1 : Integrable K1 P := hV1.1.const_mul _
  have hI2 : Integrable K2 P := hV2.1.const_mul _
  have hI3 : Integrable K3 P := hV3.1.const_mul _
  have hI4 : Integrable K4 P := hC12.1.const_mul _
  have hI5 : Integrable K5 P := hC13.1.const_mul _
  have hI6 : Integrable K6 P := hC23.1.const_mul _
  have hI12 := hI1.add hI2
  have hI123 := hI12.add hI3
  have hI1234 := hI123.add hI4
  have hI12345 := hI1234.add hI5
  have hPoly (ω : Ω) :
      (a * V1 ω + b * V2 ω + c * V3 ω) ^ 2 =
        ((((K1 ω + K2 ω) + K3 ω) + K4 ω) + K5 ω) + K6 ω := by
    dsimp [K1, K2, K3, K4, K5, K6]
    ring
  have hSqI : Integrable
      (fun ω => (a * V1 ω + b * V2 ω + c * V3 ω) ^ 2) P := by
    have hEq : (fun ω => ((((K1 ω + K2 ω) + K3 ω) + K4 ω) + K5 ω) + K6 ω)
        =ᵐ[P] (fun ω => (a * V1 ω + b * V2 ω + c * V3 ω) ^ 2) :=
      Filter.Eventually.of_forall (fun ω => (hPoly ω).symm)
    exact (hI12345.add hI6).congr hEq
  have hIntSplit :
      (∫ ω, ((((K1 ω + K2 ω) + K3 ω) + K4 ω) + K5 ω) + K6 ω ∂P) =
        (((((∫ ω, K1 ω ∂P) + (∫ ω, K2 ω ∂P)) +
            (∫ ω, K3 ω ∂P)) + (∫ ω, K4 ω ∂P)) +
            (∫ ω, K5 ω ∂P)) + (∫ ω, K6 ω ∂P) := by
    calc
      _ = (∫ ω, (((K1 ω + K2 ω) + K3 ω) + K4 ω) + K5 ω ∂P) +
          (∫ ω, K6 ω ∂P) := by exact integral_add hI12345 hI6
      _ = ((∫ ω, ((K1 ω + K2 ω) + K3 ω) + K4 ω ∂P) +
          (∫ ω, K5 ω ∂P)) + (∫ ω, K6 ω ∂P) := by
            congr 1
            exact integral_add hI1234 hI5
      _ = (((∫ ω, (K1 ω + K2 ω) + K3 ω ∂P) +
          (∫ ω, K4 ω ∂P)) + (∫ ω, K5 ω ∂P)) +
          (∫ ω, K6 ω ∂P) := by
            congr 1
            congr 1
            exact integral_add hI123 hI4
      _ = ((((∫ ω, K1 ω + K2 ω ∂P) +
          (∫ ω, K3 ω ∂P)) + (∫ ω, K4 ω ∂P)) +
          (∫ ω, K5 ω ∂P)) + (∫ ω, K6 ω ∂P) := by
            congr 1
            congr 1
            congr 1
            exact integral_add hI12 hI3
      _ = _ := by
            congr 1
            congr 1
            congr 1
            congr 1
            exact integral_add hI1 hI2
  constructor
  · exact hSqI
  · calc
      (∫ ω, (a * V1 ω + b * V2 ω + c * V3 ω) ^ 2 ∂P) =
        ∫ ω, ((((K1 ω + K2 ω) + K3 ω) + K4 ω) + K5 ω) + K6 ω ∂P := by
          exact integral_congr_ae (Filter.Eventually.of_forall hPoly)
      _ = (((((∫ ω, K1 ω ∂P) + (∫ ω, K2 ω ∂P)) +
            (∫ ω, K3 ω ∂P)) + (∫ ω, K4 ω ∂P)) +
            (∫ ω, K5 ω ∂P)) + (∫ ω, K6 ω ∂P) := hIntSplit
      _ = a ^ 2 * r n m + b ^ 2 * r m p + c ^ 2 * r p q := by
        simp only [K1, K2, K3, K4, K5, K6, integral_const_mul]
        rw [hV1.2, hV2.2, hV3.2, hC12.2, hC13.2, hC23.2]
        ring
