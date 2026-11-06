-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f2_original_positive_subcap_C1_domain_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:58:52.830874+00:00
-- url     : https://prove2.me/submissions/a84109b9-8aad-4b82-a9f1-1c454d37e4c1

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal ENNReal
noncomputable section

/-- The exact original strict positive reserve subcap is an open real domain. -/
theorem solution (C : ℝ≥0∞) :
    IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
  have hPos : IsOpen {y : ℝ | 0 < y} :=
    isOpen_lt continuous_const continuous_id
  have hCap : IsOpen {y : ℝ | ENNReal.ofReal y < C} :=
    isOpen_lt ENNReal.continuous_ofReal continuous_const
  exact hPos.inter hCap
