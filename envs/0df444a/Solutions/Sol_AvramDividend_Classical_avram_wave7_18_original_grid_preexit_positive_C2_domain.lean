-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_18_original_grid_preexit_positive_C2_domain
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:24:39.121037+00:00
-- url     : https://prove2.me/submissions/b756cd89-b93c-4016-81de-95a5769ef005

import Mathlib
import Mathlib.Probability.Process.HittingTime
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (lower upper : ℝ) (hlower : 0 < lower)
    (hcap : ∀ y ∈ Set.Icc lower upper, ENNReal.ofReal y < C)
    (clock : ℕ → ℝ≥0) (m : ℕ) (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (x + X.X (clock k) ω - rightLimit D (clock k) ω - upper)
        (lower - (x + X.X (clock k) ω - rightLimit D (clock k) ω)))
      (Set.Ioi (0 : ℝ)) 0 m ω) :
    (∀ ω, K ω ≤ m) ∧
    (∀ ω k, k < K ω →
      let z : ℝ := x + X.X (clock k) ω - rightLimit D (clock k) ω
      z ∈ Set.Icc lower upper ∧
      (0 < z ∧ ENNReal.ofReal z < C) ∧
      ContDiffWithinAt ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} z) := by
  let Z : ℕ → Ω → ℝ := fun k ω =>
    x + X.X (clock k) ω - rightLimit D (clock k) ω
  let Y : ℕ → Ω → ℝ := fun k ω =>
    max (Z k ω - upper) (lower - Z k ω)
  constructor
  · intro ω
    rw [hK ω]
    exact hittingBtwn_le ω
  · intro ω k hk
    have hlt : k < hittingBtwn Y (Set.Ioi (0 : ℝ)) 0 m ω := by
      simpa only [hK ω] using hk
    have hnonmem : Y k ω ∉ Set.Ioi (0 : ℝ) :=
      notMem_of_lt_hittingBtwn hlt (Nat.zero_le k)
    have hyle : Y k ω ≤ 0 := le_of_not_gt hnonmem
    have hupper : Z k ω - upper ≤ 0 :=
      (le_max_left (Z k ω - upper) (lower - Z k ω)).trans hyle
    have hlower' : lower - Z k ω ≤ 0 :=
      (le_max_right (Z k ω - upper) (lower - Z k ω)).trans hyle
    have hband : Z k ω ∈ Set.Icc lower upper := by
      change lower ≤ Z k ω ∧ Z k ω ≤ upper
      constructor <;> linarith
    have hdomain : 0 < Z k ω ∧ ENNReal.ofReal (Z k ω) < C :=
      ⟨lt_of_lt_of_le hlower hband.1, hcap (Z k ω) hband⟩
    change Z k ω ∈ Set.Icc lower upper ∧
      (0 < Z k ω ∧ ENNReal.ofReal (Z k ω) < C) ∧
      ContDiffWithinAt ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} (Z k ω)
    exact ⟨hband, hdomain, hw (Z k ω) hdomain⟩
