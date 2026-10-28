-- Prove2me | solution 1 for AvramDividend.Classical.levy_measurableSet_negative_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:46:24.263076+00:00
-- url     : https://prove2.me/submissions/0fee8596-445f-4c04-8454-977aef94a786

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_negative_before_horizon_iff_dense_grid
import Theorems.Thm_AvramDividend_Classical_measurableSet_countable_schedule_negative_near_zero
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε → ∃ n : ℕ, horizons n ≤ ε) :
    MeasurableSet
      {ω : Ω | ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0} := by
  have heq :
      {ω : Ω | ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0} =
      (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) ⁻¹'
        {f : ℝ≥0 → ℝ | ∀ n : ℕ, ∃ m : ℕ,
          times m < horizons n ∧ f (times m) < 0} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · intro h n
      exact (levy_negative_before_horizon_iff_dense_grid X times hdense ω
        (horizons n)).mp (h (horizons n) (hpos n))
    · intro h ε hε
      obtain ⟨n, hn⟩ := hcofinal ε hε
      obtain ⟨m, hm, hmneg⟩ := h n
      exact ⟨times m, lt_of_lt_of_le hm hn, hmneg⟩
  rw [heq]
  exact (measurableSet_countable_schedule_negative_near_zero times horizons).preimage
    (levy_wholePath_measurable X)
