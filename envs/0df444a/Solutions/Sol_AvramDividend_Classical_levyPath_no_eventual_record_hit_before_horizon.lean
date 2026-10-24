-- Prove2me | solution 1 for AvramDividend.Classical.levyPath_no_eventual_record_hit_before_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:53:43.141409+00:00
-- url     : https://prove2.me/submissions/a657d024-bdf8-4eb2-925e-7e46c7dcfaad

import Mathlib.Data.Real.Basic
import Theorems.Thm_AvramDividend_Classical_levyPath_finite_horizon_below_eventual_record_level
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-! Beyond some finite record index no grid level is crossed before the horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (ω : Ω)
    (T : ℝ≥0) (b h : ℝ) (hh : 0 < h) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t : ℝ≥0, t ≤ T →
      ¬ b + (n : ℝ) * h < X.X t ω := by
  obtain ⟨N, hN⟩ :=
    levyPath_finite_horizon_below_eventual_record_level X ω T b h hh
  refine ⟨N, ?_⟩
  intro n hn t ht hcross
  have hNat : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hm : (N : ℝ) * h ≤ (n : ℝ) * h :=
    mul_le_mul_of_nonneg_right hNat hh.le
  have hlevel : b + (N : ℝ) * h ≤ b + (n : ℝ) * h :=
    add_le_add_right hm b
  have hpath : X.X t ω < b + (n : ℝ) * h :=
    (hN t ht).trans_le hlevel
  exact (not_lt_of_ge hpath.le) hcross
