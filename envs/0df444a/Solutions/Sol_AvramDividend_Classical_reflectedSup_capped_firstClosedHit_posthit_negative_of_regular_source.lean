-- Prove2me | solution 1 for AvramDividend.Classical.reflectedSup_capped_firstClosedHit_posthit_negative_of_regular_source
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:12:25.649016+00:00
-- url     : https://prove2.me/submissions/ebab75d4-efc2-4dc9-aa85-30fae1d956a8

import Theorems.Thm_AvramDividend_Classical_reflectedSup_capped_closedLevelHit_stoppingTime
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_negative_near_zero_of_grid
import Theorems.Thm_AvramDividend_Classical_levy_negative_before_horizon_iff_dense_grid

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ℝ≥0) (x : ℝ)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε → ∃ n : ℕ, horizons n ≤ ε)
    (hRegular : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧
        X.X (sInf ((Icc (0 : ℝ≥0) H ∩
          (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H}) + s) ω -
        X.X (sInf ((Icc (0 : ℝ≥0) H ∩
          (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H})) ω < 0 := by
  have hstop := reflectedSup_capped_closedLevelHit_stoppingTime X H x
  refine levy_finiteStopping_negative_near_zero_of_grid X
    (fun ω => sInf ((Icc (0 : ℝ≥0) H ∩
      (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H})) ?_ hstop times horizons hcofinal ?_
  · intro s
    have := hstop s
    simpa only [WithTop.coe_le_coe] using this
  · filter_upwards [hRegular] with ω hω n
    exact (levy_negative_before_horizon_iff_dense_grid X times hdense ω (horizons n)).1
      (hω _ (hpos n))
