-- Prove2me | solution 1 for EpsOptimalSelection.band_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:13:19.637347+00:00
-- url     : https://prove2.me/submissions/2ebf909b-9fa0-4dcb-98b8-512907cfe9bd

import Definitions.Def_BicausalOT_DescriptiveSetTheory_Tree
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Definitions.Def_BicausalOT_DescriptiveSetTheory_EpsOptimalSelection

set_option autoImplicit false
open MeasureTheory Set ENNReal
open scoped Classical
noncomputable section
variable {H E : Type*} [TopologicalSpace H] [TopologicalSpace E]
open EpsOptimalSelection
namespace EpsOptimalSelection
theorem _root_.solution {ε' v : ℝ≥0∞} {m : ℕ}
    (hmin : ∀ j, j < m + 1 → ¬ bandPred ε' j v) :
    ((m : ℕ) : ℝ≥0∞) * ε' ≤ v := by
  cases m with
  | zero => simp
  | succ j => exact not_lt.mp (hmin (j + 1) (by omega))
end EpsOptimalSelection
