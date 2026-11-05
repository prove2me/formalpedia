-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_measurable_dividend_kernel_pathwise_disjoint_diffuse_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T20:16:47.396557+00:00
-- url     : https://prove2.me/submissions/9090b583-6fcb-4afd-912d-c3c3665a1389

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_stieltjes_restrict_atoms_diffuse_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_stieltjes_diffuse_submeasure_actual_dividend

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The true original dividend measure is a measurable s-finite kernel;
each closed-horizon path has an exactly disjoint, dominated diffuse split. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∃ κ : ProbabilityTheory.Kernel Ω ℝ,
      ProbabilityTheory.IsSFiniteKernel κ ∧
      (∀ ω : Ω, κ ω = dividendMeasure D ω) ∧
      ∀ (ω : Ω) (T : ℝ≥0),
        ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
          A.Countable ∧ MeasurableSet A ∧
          (κ ω).restrict (Icc (0 : ℝ) (T : ℝ)) = μatom + μdiffuse ∧
          ((κ ω).restrict (Icc (0 : ℝ) (T : ℝ))).restrict A = μatom ∧
          ((κ ω).restrict (Icc (0 : ℝ) (T : ℝ))).restrict Aᶜ = μdiffuse ∧
          μdiffuse ≤ κ ω ∧ NullSingletonClass μdiffuse := by
  obtain ⟨κ, hκfinite, hκ⟩ := dividendMeasure_global_sfinite_kernel_exists D hD
  refine ⟨κ, hκfinite, hκ, ?_⟩
  intro ω T
  obtain ⟨A, μatom, μdiffuse, hCount, hMeas, hsplit, hAtom,
    hDiff, hNull, _, _⟩ :=
    avram_p4_d_dividend_original_closed_stieltjes_restrict_atoms_diffuse_exact
      D hD ω T
  refine ⟨A, μatom, μdiffuse, hCount, hMeas, ?_, ?_, ?_, ?_, hNull⟩
  · simpa only [hκ ω] using hsplit
  · simpa only [hκ ω] using hAtom
  · simpa only [hκ ω] using hDiff
  · rw [hκ ω]
    exact avram_p4_d_dividend_original_closed_stieltjes_diffuse_submeasure_actual_dividend
      D ω T μatom μdiffuse hsplit
