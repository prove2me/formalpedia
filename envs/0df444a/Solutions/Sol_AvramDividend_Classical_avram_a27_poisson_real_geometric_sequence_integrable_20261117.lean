-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_poisson_real_geometric_sequence_integrable_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:32:52.796136+00:00
-- url     : https://prove2.me/submissions/deb33f45-3615-4c23-ac3d-30883b543982

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat06_poisson_count_pgf_general
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Poisson measures integrate all real-power geometric sequences. -/
theorem solution (r : ℝ≥0) (m : ℝ) :
    Integrable (fun k : ℕ => m ^ k) (poissonMeasure r) := by
  by_contra hnot
  have hp := chat06_poisson_count_pgf_general r m
  have hzero : (∫ k : ℕ, m ^ k ∂poissonMeasure r) = 0 :=
    integral_undef hnot
  rw [hzero] at hp
  exact (Real.exp_ne_zero _) hp.symm
