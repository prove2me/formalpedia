-- Prove2me | solution 1 for AvramDividend.Classical.reflectedSup_finite_horizon_max_no_positive_atom_below_terminal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:55:48.857916+00:00
-- url     : https://prove2.me/submissions/83328598-ad4b-41eb-94cc-8545a20d3fba

import Mathlib.MeasureTheory.OuterMeasure.AE
import Theorems.Thm_AvramDividend_Classical_reflectedSup_terminal_below_max_capped_first_hit_geometry
import Theorems.Thm_AvramDividend_Classical_reflectedSup_capped_firstClosedHit_posthit_negative_of_regular_source
import Theorems.Thm_AvramDividend_Classical_reflectedSup_exceeds_hit_height_of_negative_posthit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ℝ≥0) (x : ℝ≥0) (hx : 0 < x)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε → ∃ n : ℕ, horizons n ≤ ε)
    (hRegular : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0) :
    P {ω : Ω |
      sSup ((fun u : ℝ≥0 => reflectedSup X u ω) '' Icc 0 H) = (x : ℝ) ∧
      reflectedSup X H ω < (x : ℝ)} = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [reflectedSup_capped_firstClosedHit_posthit_negative_of_regular_source X H (x : ℝ)
    times horizons hdense hpos hcofinal hRegular] with ω hneg
  rintro ⟨hMax, hEnd⟩
  obtain ⟨hlt, hhit, hbound⟩ :=
    reflectedSup_terminal_below_max_capped_first_hit_geometry X ω H (x : ℝ) (by exact_mod_cast hx)
      hMax hEnd
  obtain ⟨t, -, htH, hxt⟩ := reflectedSup_exceeds_hit_height_of_negative_posthit X ω _ H x hlt hhit
    (fun ε hε => by
      obtain ⟨s, hs, h⟩ := hneg ε hε
      exact ⟨s, hs, by linarith⟩)
  linarith [hbound t htH.le]
