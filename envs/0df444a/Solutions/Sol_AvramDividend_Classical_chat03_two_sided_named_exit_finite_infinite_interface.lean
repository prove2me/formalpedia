-- Prove2me | solution 1 for AvramDividend.Classical.chat03_two_sided_named_exit_finite_infinite_interface
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T22:17:15.769332+00:00
-- url     : https://prove2.me/submissions/1fc332df-9efa-4399-9074-e19379bb72ef

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_finite_extended_infimum_isGLB
import Theorems.Thm_AvramDividend_Classical_chat03_extended_infimum_is_top_iff_no_exit
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Named official two-sided strict exit clocks have exact finite GLB and
infinity/no-crossing interfaces. All parts derive from two Proved general
ENNReal infimum theorems, without strengthened process assumptions.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (u d : ℝ) (ω : Ω) :
    (twoSidedExitUpTime X u ω ≠ ∞ →
      IsGLB {t : ℝ≥0 | u < X.X t ω}
        (twoSidedExitUpTime X u ω).toNNReal) ∧
    (twoSidedExitDownTime X d ω ≠ ∞ →
      IsGLB {t : ℝ≥0 | X.X t ω < d}
        (twoSidedExitDownTime X d ω).toNNReal) ∧
    (twoSidedExitUpTime X u ω = ∞ ↔
      ¬ ∃ t : ℝ≥0, u < X.X t ω) ∧
    (twoSidedExitDownTime X d ω = ∞ ↔
      ¬ ∃ t : ℝ≥0, X.X t ω < d) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hf
    exact chat03_finite_extended_infimum_isGLB
      (fun t => u < X.X t ω)
      (twoSidedExitUpTime X u ω) rfl hf
  · intro hf
    exact chat03_finite_extended_infimum_isGLB
      (fun t => X.X t ω < d)
      (twoSidedExitDownTime X d ω) rfl hf
  · exact chat03_extended_infimum_is_top_iff_no_exit
      (fun t => u < X.X t ω)
  · exact chat03_extended_infimum_is_top_iff_no_exit
      (fun t => X.X t ω < d)