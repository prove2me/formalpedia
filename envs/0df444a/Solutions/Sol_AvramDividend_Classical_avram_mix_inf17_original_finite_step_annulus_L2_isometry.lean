-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf17_original_finite_step_annulus_L2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T17:27:51.056407+00:00
-- url     : https://prove2.me/submissions/dc81f044-0999-40f0-af00-d0ed55e26381

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_physical_annulus_count_variance_exact
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_original_separated_annulus_compensated_covariance_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_orthogonal_finite_L2_square_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

/-- Finite deterministic original negative-mark simple functions obey the exact
compensated physical-count L² isometry. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (cut : ℕ → ℕ) (hcut : Monotone cut) (a : ℕ → ℝ) (k : ℕ) :
    let B : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((cut i : ℝ) + 1))) (-(1 / ((cut (i + 1) : ℝ) + 1)))
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B i)
    let r : ℕ → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let Y : ℕ → Ω → ℝ := fun i ω => (N i ω).toReal - r i
    Integrable (fun ω => (∑ i ∈ Finset.range k, a i * Y i ω) ^ 2) P ∧
      (∫ ω, (∑ i ∈ Finset.range k, a i * Y i ω) ^ 2 ∂P) =
        ∑ i ∈ Finset.range k, (a i) ^ 2 * r i := by
  classical
  let B : ℕ → Set ℝ := fun i =>
    Ioc (-(1 / ((cut i : ℝ) + 1))) (-(1 / ((cut (i + 1) : ℝ) + 1)))
  let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B i)
  let r : ℕ → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
  let Y : ℕ → Ω → ℝ := fun i ω => (N i ω).toReal - r i
  let F : ℕ → Ω → ℝ := fun i ω => a i * Y i ω
  let S : Finset ℕ := Finset.range k
  change Integrable (fun ω => (∑ i ∈ S, F i ω) ^ 2) P ∧
    (∫ ω, (∑ i ∈ S, F i ω) ^ 2 ∂P) =
      ∑ i ∈ S, (a i) ^ 2 * r i
  have hVar (i : ℕ) :
      Integrable (fun ω => (Y i ω) ^ 2) P ∧
      (∫ ω, (Y i ω) ^ 2 ∂P) = r i := by
    have hi : cut i ≤ cut (i + 1) := hcut (Nat.le_succ i)
    have h := avram_mixed_source13_original_physical_annulus_count_variance_exact
      X T (cut i) (cut (i + 1)) hi
    change Integrable (fun ω => (Y i ω) ^ 2) P ∧
      (∫ ω, (Y i ω) ^ 2 ∂P) = r i at h
    exact h
  have hCross (i j : ℕ) (hij : i ≠ j) :
      Integrable (fun ω => Y i ω * Y j ω) P ∧
      (∫ ω, Y i ω * Y j ω ∂P) = 0 := by
    rcases lt_or_gt_of_ne hij with hij | hji
    · have h := avram_mix_inf15_original_separated_annulus_compensated_covariance_zero
        X T (cut i) (cut (i + 1)) (cut j) (cut (j + 1))
        (hcut (Nat.le_succ i)) (hcut (Nat.succ_le_of_lt hij))
        (hcut (Nat.le_succ j))
      change Integrable (fun ω => Y i ω * Y j ω) P ∧
        (∫ ω, Y i ω * Y j ω ∂P) = 0 at h
      exact h
    · have h := avram_mix_inf15_original_separated_annulus_compensated_covariance_zero
        X T (cut j) (cut (j + 1)) (cut i) (cut (i + 1))
        (hcut (Nat.le_succ j)) (hcut (Nat.succ_le_of_lt hji))
        (hcut (Nat.le_succ i))
      change Integrable (fun ω => Y j ω * Y i ω) P ∧
        (∫ ω, Y j ω * Y i ω ∂P) = 0 at h
      have hcomm :
          (fun ω => Y j ω * Y i ω) =
            (fun ω => Y i ω * Y j ω) := by
        funext ω
        exact mul_comm _ _
      rw [hcomm] at h
      exact h
  have hSquare (i : ℕ) : Integrable (fun ω => (F i ω) ^ 2) P := by
    have heq : (fun ω => (F i ω) ^ 2) =
        (fun ω => (a i) ^ 2 * (Y i ω) ^ 2) := by
      funext ω
      dsimp [F]
      ring
    rw [heq]
    exact (hVar i).1.const_mul _
  have hProd : ∀ i ∈ S, ∀ j ∈ S,
      Integrable (fun ω => F i ω * F j ω) P := by
    intro i hi j hj
    by_cases hij : i = j
    · subst j
      have heq : (fun ω => F i ω * F i ω) =
          (fun ω => (F i ω) ^ 2) := by
        funext ω
        ring
      rw [heq]
      exact hSquare i
    · have heq : (fun ω => F i ω * F j ω) =
          (fun ω => (a i * a j) * (Y i ω * Y j ω)) := by
        funext ω
        dsimp [F]
        ring
      rw [heq]
      exact (hCross i j hij).1.const_mul _
  have hOrth : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      (∫ ω, F i ω * F j ω ∂P) = 0 := by
    intro i hi j hj hij
    have heq : (fun ω => F i ω * F j ω) =
        (fun ω => (a i * a j) * (Y i ω * Y j ω)) := by
      funext ω
      dsimp [F]
      ring
    rw [heq, integral_const_mul, (hCross i j hij).2, mul_zero]
  have hInner : ∀ i ∈ S,
      Integrable (fun ω => ∑ j ∈ S, F i ω * F j ω) P := by
    intro i hi
    exact integrable_finset_sum S (hProd i hi)
  have hSumSq : (fun ω => (∑ i ∈ S, F i ω) ^ 2) =
      (fun ω => ∑ i ∈ S, ∑ j ∈ S, F i ω * F j ω) := by
    funext ω
    simp only [pow_two, Finset.sum_mul_sum]
  have hIntegrable : Integrable (fun ω => (∑ i ∈ S, F i ω) ^ 2) P := by
    rw [hSumSq]
    exact integrable_finset_sum S hInner
  have hIsometry := avram_p4_b_smalljump_orthogonal_finite_L2_square_identity
    S F hProd hOrth
  constructor
  · exact hIntegrable
  · calc
      (∫ ω, (∑ i ∈ S, F i ω) ^ 2 ∂P) =
          ∑ i ∈ S, ∫ ω, (F i ω) ^ 2 ∂P := hIsometry
      _ = ∑ i ∈ S, (a i) ^ 2 * r i := by
        apply Finset.sum_congr rfl
        intro i hi
        have heq : (fun ω => (F i ω) ^ 2) =
            (fun ω => (a i) ^ 2 * (Y i ω) ^ 2) := by
          funext ω
          dsimp [F]
          ring
        rw [heq, integral_const_mul, (hVar i).2]
