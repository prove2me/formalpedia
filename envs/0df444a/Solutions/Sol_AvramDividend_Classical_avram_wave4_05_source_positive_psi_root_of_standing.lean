-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_positive_psi_root_of_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:29:50.848998+00:00
-- url     : https://prove2.me/submissions/387123f4-0b71-489a-914c-de03eccad848

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Defs.Filter
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_zero
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_continuousOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_standing
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
/-- Positive q-root of the actual source Lévy exponent under Standing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) :
    ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q := by
  obtain ⟨β₀, hβ₀, hbeyond⟩ :=
    psi_eventually_gt_of_standing X hX q hq
  let B : ℝ := max β₀ 0
  have hB : 0 ≤ B := le_max_right β₀ 0
  have hβB : β₀ ≤ B := le_max_left β₀ 0
  have hsubset : Icc (0 : ℝ) B ⊆ Ici (0 : ℝ) := by
    intro x hx
    exact hx.1
  have hcont : ContinuousOn X.ψ (Icc (0 : ℝ) B) :=
    (levy_laplace_exponent_continuousOn_nonnegative X).mono hsubset
  have hval : q ∈ Icc (X.ψ 0) (X.ψ B) := by
    change X.ψ 0 ≤ q ∧ q ≤ X.ψ B
    constructor
    · rw [levy_laplace_exponent_zero X]
      exact hq.le
    · exact (hbeyond B hβB).le
  obtain ⟨φ, hφrange, hroot⟩ :=
    (intermediate_value_Icc hB hcont) hval
  have hφ : 0 < φ := by
    by_contra hn
    have heq : φ = 0 := le_antisymm (le_of_not_gt hn) hφrange.1
    rw [heq, levy_laplace_exponent_zero X] at hroot
    linarith
  exact ⟨φ, hφ, hroot⟩
