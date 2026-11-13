-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a34_original_clipped_source_le_runningSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T11:26:06.466204+00:00
-- url     : https://prove2.me/submissions/820ac3af-3d57-43df-95d8-6c37b5ff7f83

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : ∀ t ω, 0 ≤ rightLimit D t ω)
    (n : ℝ≥0) (ρ : Ω → ℝ≥0) (hρ : ∀ ω, ρ ω ≤ n)
    (m : Nat) (ω : Ω) :
    let dt : ℝ≥0 := n / ((m : ℝ≥0) + 1)
    let v : Nat → ℝ≥0 := fun i => min ((i : ℝ≥0) * dt) (ρ ω)
    x + X.X (v (m + 1)) ω - rightLimit D (v m) ω ≤
      x + runningSup X n ω := by
  have hstop :
      min (((m + 1 : Nat) : ℝ≥0) *
        (n / ((m : ℝ≥0) + 1))) (ρ ω) ≤ n :=
    le_trans (min_le_right _ _) (hρ ω)
  have hsource : X.X (min (((m + 1 : Nat) : ℝ≥0) *
      (n / ((m : ℝ≥0) + 1))) (ρ ω)) ω ≤
      runningSup X n ω := by
    calc
      X.X (min (((m + 1 : Nat) : ℝ≥0) *
          (n / ((m : ℝ≥0) + 1))) (ρ ω)) ω ≤
          runningSup X (min (((m + 1 : Nat) : ℝ≥0) *
          (n / ((m : ℝ≥0) + 1))) (ρ ω)) ω :=
        (runningSup_monotone_and_path_le X ω).2 _
      _ ≤ runningSup X n ω :=
        (runningSup_monotone_and_path_le X ω).1 hstop
  have hdiv := hD (min ((m : ℝ≥0) *
      (n / ((m : ℝ≥0) + 1))) (ρ ω)) ω
  dsimp
  linarith
