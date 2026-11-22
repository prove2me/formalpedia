-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_original_anyactivity_physical_reciprocal_annulus_uniform_L2_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T13:03:01.03349+00:00
-- url     : https://prove2.me/submissions/616fc6cf-9017-428d-987a-e4477756c325

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_allnu_finite_reciprocal_L2_integrable_public
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_original_physical_reciprocal_variance_le_4V
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_real_quadratic_strip_uniform_tail
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) :
    let B : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 |
        0 < s ∧ X.X s ω -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let r : ℕ → ℝ := fun i =>
      ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let S : ℕ → ℕ → Ω → ℝ := fun n m ω =>
      ∑ i ∈ Finset.Ico n m,
        (-(1 / ((i : ℝ) + 1))) *
          ((NX ω (Ioc 0 T ×ˢ B i)).toReal - r i)
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ m : ℕ, n ≤ m →
        Integrable (fun ω => (S n m ω) ^ 2) P ∧
          (∫ ω, (S n m ω) ^ 2 ∂P) < ε := by
  intro B NX r S ε hε
  have hT : (0 : ℝ) ≤ (T : ℝ) := by positivity
  have hScale : 0 < 4 * ((T : ℝ) + 1) := by positivity
  have hSmall : 0 < ε / (4 * ((T : ℝ) + 1)) := by positivity
  obtain ⟨N, hN⟩ :=
    avram_p4_h_gaussian_original_real_quadratic_strip_uniform_tail
      X (ε / (4 * ((T : ℝ) + 1))) hSmall
  refine ⟨N, ?_⟩
  intro n hn m hnm
  have hI :
      Integrable (fun ω => (S n m ω) ^ 2) P := by
    simpa only [] using
      (avram_twoagentA_original_allnu_finite_reciprocal_L2_integrable_public
        X T n m hnm)
  have hV :
      (∫ ω, (S n m ω) ^ 2 ∂P) ≤
        4 * ((T : ℝ) *
          (∫ z in Ioc (-(1 / ((n : ℝ) + 1)))
            (-(1 / ((m : ℝ) + 1))), z ^ 2 ∂X.ν)) := by
    simpa only [] using
      (avram_twoagentA_shared_original_physical_reciprocal_variance_le_4V
        X T n m hnm)
  have hQ := (hN n hn m).2
  have hQnonneg :
      0 ≤ (∫ z in Ioc (-(1 / ((n : ℝ) + 1)))
        (-(1 / ((m : ℝ) + 1))), z ^ 2 ∂X.ν) := by
    apply integral_nonneg
    intro z
    positivity
  have hBound : 4 * ((T : ℝ) *
      (∫ z in Ioc (-(1 / ((n : ℝ) + 1)))
        (-(1 / ((m : ℝ) + 1))), z ^ 2 ∂X.ν)) < ε := by
    have hMul := mul_lt_mul_of_pos_left hQ hScale
    have hCancel :
        4 * ((T : ℝ) + 1) *
          (ε / (4 * ((T : ℝ) + 1))) = ε := by
      field_simp [ne_of_gt hScale]
    rw [hCancel] at hMul
    nlinarith
  exact ⟨hI, lt_of_le_of_lt hV hBound⟩

