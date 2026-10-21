-- Prove2me | solution 1 for AvramDividend.Classical.kernel_isSFinite_of_pointwise_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T10:38:30.211403+00:00
-- url     : https://prove2.me/submissions/3c1de108-003c-4e6f-9733-a053c202ae54

import Mathlib.Probability.Kernel.Defs
import Theorems.Thm_AvramDividend_Classical_kernel_cutoff_finite_exists
import Theorems.Thm_AvramDividend_Classical_measurable_finite_mass_bin
import Theorems.Thm_AvramDividend_Classical_finite_ennreal_mass_bin_unique
import Theorems.Thm_AvramDividend_Classical_kernel_sum_unique_partition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (κ : ProbabilityTheory.Kernel Ω ℝ)
    (hfinite : ∀ ω : Ω, (κ ω) Set.univ < ⊤) :
    ProbabilityTheory.IsSFiniteKernel κ := by
  classical
  let mass : Ω → ℝ≥0∞ := fun ω => (κ ω) Set.univ
  have hmassMeas : Measurable mass :=
    κ.measurable_coe MeasurableSet.univ
  let S : ℕ → Set Ω := fun n =>
    {ω | mass ω ≤ (n + 1 : ℝ≥0∞) ∧
      (n = 0 ∨ (n : ℝ≥0∞) < mass ω)}
  have hS : ∀ n : ℕ, MeasurableSet (S n) := by
    intro n
    exact measurable_finite_mass_bin mass hmassMeas n
  have hpart : ∀ ω : Ω, ∃! n : ℕ, ω ∈ S n := by
    intro ω
    exact finite_ennreal_mass_bin_unique (mass ω) (hfinite ω)
  have hcut (n : ℕ) :
      ∃ κCut : ProbabilityTheory.Kernel Ω ℝ,
        (∀ ω : Ω, κCut ω =
          if ω ∈ S n then κ ω else (0 : Measure ℝ)) ∧
        ProbabilityTheory.IsFiniteKernel κCut := by
    have hbnd : ∀ ω : Ω, ω ∈ S n →
        (κ ω) Set.univ ≤ (n + 1 : ℝ≥0∞) := by
      intro ω hω
      exact hω.1
    have hC : (n + 1 : ℝ≥0∞) < ⊤ := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (ENNReal.natCast_lt_top (n + 1))
    obtain ⟨κCut, hselector, hfiniteCut⟩ :=
      kernel_cutoff_finite_exists κ (S n) (hS n)
        (n + 1 : ℝ≥0∞) hC hbnd
    refine ⟨κCut, ?_, hfiniteCut⟩
    intro ω
    by_cases hω : ω ∈ S n
    · simpa only [if_pos hω] using (hselector ω)
    · simpa only [if_neg hω] using (hselector ω)
  choose κs heq hfin using hcut
  refine ⟨⟨κs, hfin, ?_⟩⟩
  apply kernel_sum_unique_partition κ S κs hpart
  intro n ω
  by_cases hω : ω ∈ S n
  · simpa only [if_pos hω] using (heq n ω)
  · simpa only [if_neg hω] using (heq n ω)
