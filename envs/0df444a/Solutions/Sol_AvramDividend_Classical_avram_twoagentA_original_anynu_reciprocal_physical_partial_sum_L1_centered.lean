-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_original_anynu_reciprocal_physical_partial_sum_L1_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T13:50:08.092793+00:00
-- url     : https://prove2.me/submissions/8e09505c-27b5-4830-b6f8-a006f05a8144

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_original_finite_negative_band_facts
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anynu_finite_negative_Borel_mark_compensated_real_L1_centered
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
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
    let F : Ω → ℝ := fun ω =>
      ∑ i ∈ Finset.range n,
        (-(1 / ((i : ℝ) + 1))) *
          ((NX ω (Ioc 0 T ×ˢ B i)).toReal - r i)
    Integrable F P ∧ (∫ ω, F ω ∂P) = 0 := by
  classical
  intro B NX r F
  have hFacts (i : ℕ) :
      MeasurableSet (B i) ∧ B i ⊆ Iio (0 : ℝ) ∧ X.ν (B i) < ⊤ := by
    simpa only [B, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]
      using (avram_twoagentA_shared_original_finite_negative_band_facts X i (i + 1))
  have hCell (i : ℕ) :
      Integrable (fun ω => (NX ω (Ioc 0 T ×ˢ B i)).toReal - r i) P ∧
        (∫ ω, (NX ω (Ioc 0 T ×ˢ B i)).toReal - r i ∂P) = 0 := by
    have h := avram_jump6_B_original_anynu_finite_negative_Borel_mark_compensated_real_L1_centered
      X 0 T (show (0 : ℝ≥0) ≤ T by positivity) (B i) (hFacts i).1 (hFacts i).2.2
      (hFacts i).2.1
    simpa only [r, tsub_zero] using h
  let c : ℕ → ℝ := fun i => -(1 / ((i : ℝ) + 1))
  have hEach : ∀ i ∈ Finset.range n,
      Integrable (fun ω => c i * ((NX ω (Ioc 0 T ×ˢ B i)).toReal - r i)) P := by
    intro i hi
    exact (hCell i).1.const_mul (c i)
  have hFI : Integrable F P := by
    simpa only [F, c] using integrable_finset_sum (Finset.range n) hEach
  refine ⟨hFI, ?_⟩
  change (∫ ω, ∑ i ∈ Finset.range n,
      c i * ((NX ω (Ioc 0 T ×ˢ B i)).toReal - r i) ∂P) = 0
  calc
    (∫ ω, ∑ i ∈ Finset.range n,
        c i * ((NX ω (Ioc 0 T ×ˢ B i)).toReal - r i) ∂P) =
      ∑ i ∈ Finset.range n,
        (∫ ω, c i * ((NX ω (Ioc 0 T ×ˢ B i)).toReal - r i) ∂P) :=
          integral_finset_sum (Finset.range n) hEach
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [integral_const_mul]
      simp only [(hCell i).2, mul_zero]
