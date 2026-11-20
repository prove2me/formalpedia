-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_finite_barrier_first_size2_mark_ruin_time_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:17:37.593455+00:00
-- url     : https://prove2.me/submissions/a4de2721-dc55-4afb-8084-fdf955748a2c

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_before_upcrossing
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_finite_barrier_risk_strict_negative_at_physical_size2_first_mark
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_negative_controlled_reserve_bounds_original_ruin_time
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (B : ℝ≥0 → ℝ) (N : ℝ≥0 → ℕ)
    (σ : ℝ≥0)
    (hPath : ∀ t : ℝ≥0, X.X t ω = B t - 2 * (N t : ℝ))
    (hTube : ∀ t : ℝ≥0, t ≤ σ → |B t| < (1 / 4000 : ℝ))
    (hBefore : ∀ t : ℝ≥0, t < σ → N t = 0)
    (hMark : 1 ≤ N σ) :
    ruinTime X (1 / 10 : ℝ)
      (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω =
      (σ : ℝ≥0∞) := by
  have hPay (t : ℝ≥0) (ht : t ≤ σ) :
      barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ) t ω = 0 := by
    apply barrierStrategy_zero_before_upcrossing
    intro s hs
    rw [hPath s]
    have hb : B s < (1 / 4000 : ℝ) :=
      (abs_lt.mp (hTube s (hs.trans ht))).2
    have hn : (0 : ℝ) ≤ (N s : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hRuinge : (σ : ℝ≥0∞) ≤
      ruinTime X (1 / 10 : ℝ)
        (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω := by
    unfold ruinTime
    refine le_iInf fun t => le_iInf fun hneg => ?_
    by_contra hnot
    have ht : t < σ := by
      exact_mod_cast (lt_of_not_ge hnot)
    have hp := hPay t (le_of_lt ht)
    have hb := (abs_lt.mp (hTube t (le_of_lt ht))).1
    have hzero := hBefore t ht
    change (1 / 10 : ℝ) + X.X t ω -
      barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ) t ω < 0 at hneg
    rw [hp, hPath t, hzero] at hneg
    norm_num at hneg
    linarith
  have hNegative :=
    avram_jump6_A_original_finite_barrier_risk_strict_negative_at_physical_size2_first_mark
      X ω B N σ hPath hTube hMark
  have hRuinle :=
    avram_jump6_A_actual_negative_controlled_reserve_bounds_original_ruin_time
      X (1 / 10 : ℝ)
        (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ))
        ω σ hNegative
  exact le_antisymm hRuinle hRuinge
