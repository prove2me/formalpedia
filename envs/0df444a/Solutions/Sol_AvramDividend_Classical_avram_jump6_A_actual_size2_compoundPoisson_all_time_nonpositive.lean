-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_actual_size2_compoundPoisson_all_time_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T09:51:53.242906+00:00
-- url     : https://prove2.me/submissions/dd906688-4239-4edb-8b8a-3ca5df9d968b

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (τ Y : ℕ → Ω → ℝ)
    (hJ : IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      (Measure.dirac (-2 : ℝ)) μ) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ,
      compoundPoisson (0 : ℝ) τ Y t ω ≤ 0 := by
  letI : IsProbabilityMeasure μ := hJ.indep.isProbabilityMeasure
  have hMarks : ∀ᵐ ω ∂μ, ∀ n : ℕ, Y n ω = (-2 : ℝ) :=
    (ae_all_iff).2 (fun n => (hJ.law_mark n).ae_eq_of_dirac)
  filter_upwards [hMarks] with ω hY
  intro t
  simp [compoundPoisson, piecewisePath, hY, Finset.sum_const, nsmul_eq_mul]
