-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_ruinclipped_predictable_two_noise_mesh_gains_zero_at_zero_stop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T23:53:18.342191+00:00
-- url     : https://prove2.me/submissions/baf0b005-fff5-4196-8055-ec570a01d416

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} (σ : Ω → ℝ≥0)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (S : Finset ℕ) (a b : ℕ → ℝ≥0)
    (WG WJ : ℕ → Ω → ℝ)
    (ω : Ω) (hσzero : σ ω = 0) :
    (∑ i ∈ S, (if σ ω ≤ a i then 0 else WG i ω) *
      (R (b i) ω - R (a i) ω)) = 0 ∧
    (∑ i ∈ S, (if σ ω ≤ a i then 0 else WJ i ω) *
      (Jsmall (b i) ω - Jsmall (a i) ω)) = 0 := by
  constructor <;> simp [hσzero]
