-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_18_original_monotone_grid_exit_clock_localisation_sequence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:02:42.26565+00:00
-- url     : https://prove2.me/submissions/e2a05786-9f44-4523-9369-1a8d3ab622e9

import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Process.HittingTime
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_grid_exit_clock_isStoppingTime_rightCont
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_grid_preexit_positive_C2_domain

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (lower upper : ℝ) (hlower : 0 < lower)
    (hcap : ∀ y ∈ Set.Icc lower upper, ENNReal.ofReal y < C)
    (clock : ℕ → ℝ≥0) (hclock : Monotone clock)
    (H : Filtration ℕ mΩ)
    (hH : ∀ k, H k = 𝓕.rightCont (clock k))
    (K : ℕ → Ω → ℕ)
    (hK : ∀ m ω, K m ω = hittingBtwn
      (fun k ω => max (x + X.X (clock k) ω - rightLimit D (clock k) ω - upper)
        (lower - (x + X.X (clock k) ω - rightLimit D (clock k) ω)))
      (Set.Ioi (0 : ℝ)) 0 m ω) :
    (∀ m, IsStoppingTime 𝓕.rightCont
      (fun ω : Ω => (clock (K m ω) : WithTop ℝ≥0))) ∧
    (∀ ω : Ω, Monotone (fun m : ℕ => (clock (K m ω) : WithTop ℝ≥0))) ∧
    (∀ m ω, K m ω ≤ m) ∧
    (∀ m ω k, k < K m ω →
      (0 < (x + X.X (clock k) ω - rightLimit D (clock k) ω) ∧
       ENNReal.ofReal (x + X.X (clock k) ω - rightLimit D (clock k) ω) < C) ∧
      ContDiffWithinAt ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}
        (x + X.X (clock k) ω - rightLimit D (clock k) ω)) := by
  constructor
  · intro m
    exact avram_wave7_18_original_grid_exit_clock_isStoppingTime_rightCont
      X x D hD clock hclock H hH lower upper m (K m) (hK m)
  constructor
  · intro ω a b hab
    have hKab : K a ω ≤ K b ω := by
      rw [hK a ω, hK b ω]
      have hmono : Monotone (fun r : ℕ =>
          hittingBtwn (fun k ω => max (x + X.X (clock k) ω - rightLimit D (clock k) ω - upper)
            (lower - (x + X.X (clock k) ω - rightLimit D (clock k) ω)))
            (Set.Ioi (0 : ℝ)) 0 r ω) :=
        hittingBtwn_mono_right
          (fun k ω => max (x + X.X (clock k) ω - rightLimit D (clock k) ω - upper)
            (lower - (x + X.X (clock k) ω - rightLimit D (clock k) ω)))
          (Set.Ioi (0 : ℝ)) 0
      exact hmono hab
    exact WithTop.coe_le_coe.mpr (hclock hKab)
  constructor
  · intro m ω
    rw [hK m ω]
    exact hittingBtwn_le ω
  · intro m ω k hk
    have hloc :=
      (avram_wave7_18_original_grid_preexit_positive_C2_domain
        X x D C w hw lower upper hlower hcap clock m (K m) (hK m)).2 ω k hk
    exact ⟨hloc.2.1, hloc.2.2⟩
