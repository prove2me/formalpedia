-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a65_ofReal_liminf_from_real_eventual_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:01:17.21542+00:00
-- url     : https://prove2.me/submissions/bd4767bf-c1f7-4696-bd8a-f57c281bde3d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section

theorem solution
    (a : ℝ) (u : ℕ → ℝ)
    (hLower : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in (atTop : Filter ℕ), a - ε < u n) :
    ENNReal.ofReal a ≤ liminf (fun n : ℕ => ENNReal.ofReal (u n)) atTop := by
  by_cases ha : a ≤ 0
  · have hz : ENNReal.ofReal a = 0 := ENNReal.ofReal_eq_zero.mpr ha
    simp [hz]
  · have hapos : 0 < a := lt_of_not_ge ha
    apply (Filter.le_liminf_iff).2
    intro b hb
    have hNotTop : b ≠ ⊤ := by
      intro h
      simp [h] at hb
    have hBr : b.toReal < a := by
      have h := (ENNReal.toReal_lt_toReal hNotTop ENNReal.ofReal_ne_top).2 hb
      simpa only [ENNReal.toReal_ofReal (le_of_lt hapos)] using h
    let ε : ℝ := (a - b.toReal) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    filter_upwards [hLower ε hε] with n hn
    have hNu : b.toReal < u n := by dsimp [ε] at hn; linarith
    have hUp : 0 < u n :=
      lt_of_le_of_lt ENNReal.toReal_nonneg hNu
    calc
      b = ENNReal.ofReal b.toReal := (ENNReal.ofReal_toReal hNotTop).symm
      _ < ENNReal.ofReal (u n) :=
        (ENNReal.ofReal_lt_ofReal_iff hUp).2 hNu
