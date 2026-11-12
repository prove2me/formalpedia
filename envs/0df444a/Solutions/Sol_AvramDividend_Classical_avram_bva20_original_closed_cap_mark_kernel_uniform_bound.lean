-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva20_original_closed_cap_mark_kernel_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:45:17.422787+00:00
-- url     : https://prove2.me/submissions/53634720-6974-46b8-a0e4-eb1a36e02222

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva20_original_inclusive_finite_cap_compact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original closed cap carries one finite absolute negative-mark kernel bound. -/
theorem solution
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤) (ψ : ℝ → ℝ)
    (hKernel : ∀ s : Set ℝ, IsCompact s →
      s ⊆ {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C} →
      UniformContinuousOn ψ s) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ b : ℝ, 0 ≤ b → ENNReal.ofReal b ≤ C → |ψ b| ≤ B := by
  let s : Set ℝ := {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C}
  have hs : IsCompact s :=
    avram_bva20_original_inclusive_finite_cap_compact C hFinite
  have hc : ContinuousOn ψ s :=
    (hKernel s hs (subset_rfl)).continuousOn
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuousOn hc
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro b hb hbC
  have hbm : ‖ψ b‖ ≤ M := hM b ⟨hb, hbC⟩
  calc
    |ψ b| = ‖ψ b‖ := (Real.norm_eq_abs _).symm
    _ ≤ M := hbm
    _ ≤ max M 0 := le_max_left _ _
