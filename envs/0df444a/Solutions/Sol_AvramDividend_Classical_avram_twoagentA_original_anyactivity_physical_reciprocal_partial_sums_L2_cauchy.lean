-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_original_anyactivity_physical_reciprocal_partial_sums_L2_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T13:14:16.977864+00:00
-- url     : https://prove2.me/submissions/1d7db6ee-7d2b-4517-a7f3-8838c680331b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_anyactivity_physical_reciprocal_annulus_uniform_L2_tail
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section
set_option autoImplicit false

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
    let F : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ Finset.range n,
        (-(1 / ((i : ℝ) + 1))) *
          ((NX ω (Ioc 0 T ×ˢ B i)).toReal - r i)
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ m : ℕ, N ≤ m →
        Integrable (fun ω => (F n ω - F m ω) ^ 2) P ∧
          (∫ ω, (F n ω - F m ω) ^ 2 ∂P) < ε := by
  classical
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
  let F : ℕ → Ω → ℝ := fun n ω =>
    ∑ i ∈ Finset.range n,
      (-(1 / ((i : ℝ) + 1))) *
        ((NX ω (Ioc 0 T ×ˢ B i)).toReal - r i)
  change ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n →
      ∀ m, N ≤ m →
        Integrable (fun ω => (F n ω - F m ω) ^ 2) P ∧
          (∫ ω, (F n ω - F m ω) ^ 2 ∂P) < ε
  have hTail : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n →
      ∀ m, n ≤ m →
        Integrable (fun ω => (S n m ω) ^ 2) P ∧
          (∫ ω, (S n m ω) ^ 2 ∂P) < ε :=
    avram_twoagentA_original_anyactivity_physical_reciprocal_annulus_uniform_L2_tail X T
  have hSpan (n m : ℕ) (hnm : n ≤ m) (ω : Ω) :
      F m ω - F n ω = S n m ω := by
    dsimp [F, S]
    rw [Finset.sum_Ico_eq_sub]
    exact hnm
  intro ε hε
  obtain ⟨N, hN⟩ := hTail ε hε
  refine ⟨N, ?_⟩
  intro n hn m hm
  rcases le_total n m with hnm | hmn
  · have hEq : (fun ω => (F n ω - F m ω) ^ 2) =
        (fun ω => (S n m ω) ^ 2) := by
      funext ω
      rw [← hSpan n m hnm ω]
      ring
    rw [hEq]
    exact hN n hn m hnm
  · have hEq : (fun ω => (F n ω - F m ω) ^ 2) =
        (fun ω => (S m n ω) ^ 2) := by
      funext ω
      rw [hSpan m n hmn ω]
    rw [hEq]
    exact hN m hm n hmn
