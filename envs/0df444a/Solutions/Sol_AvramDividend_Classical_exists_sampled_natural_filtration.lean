-- Prove2me | solution 1 for AvramDividend.Classical.exists_sampled_natural_filtration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:56:00.198662+00:00
-- url     : https://prove2.me/submissions/4534024c-3dc8-4615-852f-46ae7542699b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) :
    ∃ 𝓖 : Filtration ℕ mΩ, ∀ n : ℕ, 𝓖 n = 𝓕 (n : ℝ≥0) := by
  let 𝓖 : Filtration ℕ mΩ := {
    seq := fun n => 𝓕 (n : ℝ≥0)
    mono' := by
      intro i j hij
      exact 𝓕.mono (by exact_mod_cast hij)
    le' := fun n => 𝓕.le (n : ℝ≥0)
  }
  exact ⟨𝓖, fun n => rfl⟩
