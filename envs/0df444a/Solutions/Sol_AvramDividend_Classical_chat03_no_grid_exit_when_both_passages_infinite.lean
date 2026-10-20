-- Prove2me | solution 1 for AvramDividend.Classical.chat03_no_grid_exit_when_both_passages_infinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T22:15:43.082994+00:00
-- url     : https://prove2.me/submissions/6eada141-461e-4594-a4f2-b2567ebc8305

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_extended_infimum_is_top_iff_no_exit
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Both official strict first-passage times infinite means there is no real
strict two-sided exit at any time, hence none on any uniform grid.
This covers the no-exit branch absent from finite IsGLB mesh convergence.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ)
    (hUp : twoSidedExitUpTime X upper ω = ∞)
    (hDown : twoSidedExitDownTime X lower ω = ∞) :
    (∀ t : ℝ≥0,
      ¬ (X.X t ω < lower ∨ upper < X.X t ω)) ∧
    (∀ h : ℝ≥0, ∀ k : ℕ,
      ¬ (X.X ((k : ℝ≥0) * h) ω < lower ∨
         upper < X.X ((k : ℝ≥0) * h) ω)) := by
  have hNoUp : ¬ ∃ t : ℝ≥0, upper < X.X t ω :=
    (chat03_extended_infimum_is_top_iff_no_exit
      (fun t : ℝ≥0 => upper < X.X t ω)).mp hUp
  have hNoDown : ¬ ∃ t : ℝ≥0, X.X t ω < lower :=
    (chat03_extended_infimum_is_top_iff_no_exit
      (fun t : ℝ≥0 => X.X t ω < lower)).mp hDown
  have hNone : ∀ t : ℝ≥0,
      ¬ (X.X t ω < lower ∨ upper < X.X t ω) := by
    intro t ht
    rcases ht with hd | hu
    · exact hNoDown ⟨t, hd⟩
    · exact hNoUp ⟨t, hu⟩
  exact ⟨hNone, fun h k => hNone ((k : ℝ≥0) * h)⟩
