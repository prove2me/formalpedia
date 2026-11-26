-- Prove2me | solution 1 for EpsOptimalSelection.exists_band
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:13:10.340805+00:00
-- url     : https://prove2.me/submissions/41cc74fc-745f-4d4e-8626-e91b147ad1f4

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
theorem _root_.solution {ε' : ℝ≥0∞} (hε'0 : 0 < ε') (hε'top : ε' ≠ ∞)
    (v : ℝ≥0∞) : ∃ m : ℕ, bandPred ε' m v := by
  by_cases hv : v = ∞
  · exact ⟨0, hv⟩
  · obtain ⟨n, hn⟩ :=
      ENNReal.exists_nat_gt (ENNReal.div_lt_top hv hε'0.ne').ne
    have hvn : v < (n : ℝ≥0∞) * ε' :=
      (ENNReal.div_lt_iff (Or.inl hε'0.ne') (Or.inl hε'top)).mp hn
    rcases n with _ | m
    · exact absurd hvn (by simp)
    · exact ⟨m + 1, hvn⟩
end EpsOptimalSelection
