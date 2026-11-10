-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf17_ordered_finite_physical_mark_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T18:02:01.665348+00:00
-- url     : https://prove2.me/submissions/57c07a0a-015a-44da-9391-ef34d2fa8f20

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_finite_grid_L2_isometry_from_unweighted_moments
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_physical_annulus_count_variance_exact
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_original_separated_annulus_compensated_covariance_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Finite ordered physical annuli admit exact deterministic simple-mark L² isometry. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (S : Finset ℕ) (a b : ℕ → ℕ)
    (hLe : ∀ i ∈ S, a i ≤ b i)
    (hSep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      b i ≤ a j ∨ b j ≤ a i) (c : ℕ → ℝ) :
    let B : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((a i : ℝ) + 1))) (-(1 / ((b i : ℝ) + 1)))
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B i)
    let r : ℕ → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
    (∫ ω, (∑ i ∈ S, c i * ((N i ω).toReal - r i)) ^ 2 ∂P) =
      ∑ i ∈ S, c i ^ 2 * r i := by
  classical
  let B : ℕ → Set ℝ := fun i =>
    Ioc (-(1 / ((a i : ℝ) + 1))) (-(1 / ((b i : ℝ) + 1)))
  let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B i)
  let J : ℕ → Ω → ℝ := fun i ω => (N i ω).toReal
  let r : ℕ → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
  change (∫ ω, (∑ i ∈ S, c i * (J i ω - r i)) ^ 2 ∂P) =
    ∑ i ∈ S, c i ^ 2 * r i
  have hVarInt : ∀ i ∈ S,
      Integrable (fun ω => (J i ω - r i) ^ 2) P ∧
      (∫ ω, (J i ω - r i) ^ 2 ∂P) = r i := by
    intro i hi
    have h := avram_mixed_source13_original_physical_annulus_count_variance_exact
      X T (a i) (b i) (hLe i hi)
    change Integrable (fun ω => (J i ω - r i) ^ 2) P ∧
      (∫ ω, (J i ω - r i) ^ 2 ∂P) = r i at h
    exact h
  have hCross : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      Integrable (fun ω => (J i ω - r i) * (J j ω - r j)) P ∧
      (∫ ω, (J i ω - r i) * (J j ω - r j) ∂P) = 0 := by
    intro i hi j hj hij
    rcases hSep i hi j hj hij with hij' | hji'
    · have h := avram_mix_inf15_original_separated_annulus_compensated_covariance_zero
        X T (a i) (b i) (a j) (b j) (hLe i hi) hij' (hLe j hj)
      change Integrable (fun ω => (J i ω - r i) * (J j ω - r j)) P ∧
        (∫ ω, (J i ω - r i) * (J j ω - r j) ∂P) = 0 at h
      exact h
    · have h := avram_mix_inf15_original_separated_annulus_compensated_covariance_zero
        X T (a j) (b j) (a i) (b i) (hLe j hj) hji' (hLe i hi)
      change Integrable (fun ω => (J j ω - r j) * (J i ω - r i)) P ∧
        (∫ ω, (J j ω - r j) * (J i ω - r i) ∂P) = 0 at h
      have hcomm : (fun ω => (J j ω - r j) * (J i ω - r i)) =
          (fun ω => (J i ω - r i) * (J j ω - r j)) := by
        funext ω
        ring
      rw [hcomm] at h
      exact h
  have hPairInt : ∀ i ∈ S, ∀ j ∈ S,
      Integrable (fun ω =>
        (c i * (J i ω - r i)) * (c j * (J j ω - r j))) P := by
    intro i hi j hj
    by_cases hij : i = j
    · subst j
      convert (hVarInt i hi).1.const_mul (c i ^ 2) using 1
      funext ω
      ring
    · convert (hCross i hi j hj hij).1.const_mul (c i * c j) using 1
      funext ω
      ring
  exact avram_p4_b_smalljump_original_finite_grid_L2_isometry_from_unweighted_moments
    X 0 T S B J
    (by intro i hi ω; rfl) r c
    (by intro i hi; simp only [r, tsub_zero]) hPairInt
    (by intro i hi; exact (hVarInt i hi).2)
    (by intro i hi j hj hij; exact (hCross i hi j hj hij).2)
