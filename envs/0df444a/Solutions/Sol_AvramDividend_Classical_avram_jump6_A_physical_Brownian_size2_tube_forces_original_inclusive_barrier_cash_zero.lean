-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_physical_Brownian_size2_tube_forces_original_inclusive_barrier_cash_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:25:23.972385+00:00
-- url     : https://prove2.me/submissions/868f4919-987f-475b-9d33-b0550de833fe

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_preUpcrossing_stieltjesReward_zero
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_cap_tube_below_barrier_implies_upper_exit_clock_after_stop
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
    (σ u : ℝ≥0)
    (hPath : ∀ t : ℝ≥0, X.X t ω = B t - 2 * (N t : ℝ))
    (hTube : ∀ t : ℝ≥0, t ≤ σ → |B t| < (1 / 4000 : ℝ))
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0)
        (_ : (1 / 5 : ℝ) - (1 / 10 : ℝ) < X.X s ω),
        (s : ℝ≥0∞)))
    (q : ℝ) :
    (∫⁻ s in paymentTimes
        (ruinTime X (1 / 10 : ℝ)
          (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω) ∩
        Iic (σ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure
            (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω)) = 0 := by
  have hBound : ∀ s : ℝ≥0, s ≤ σ →
      X.X s ω ≤ (1 / 5 : ℝ) - (1 / 10 : ℝ) := by
    intro s hs
    rw [hPath s]
    have hb : B s < (1 / 4000 : ℝ) := (abs_lt.mp (hTube s hs)).2
    have hn : (0 : ℝ) ≤ (N s : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hσ :
      σ ≤ u :=
    avram_jump6_A_original_cap_tube_below_barrier_implies_upper_exit_clock_after_stop
      X (1 / 10 : ℝ) (1 / 5 : ℝ) ω u σ hu hBound
  have hBase := barrierStrategy_preUpcrossing_stieltjesReward_zero
    X (1 / 10 : ℝ) (1 / 5 : ℝ) (by norm_num) (by norm_num)
    ω u hu (fun s : ℝ => ENNReal.ofReal (Real.exp (-(q * s))))
  have hReal : (σ : ℝ) ≤ (u : ℝ) := by exact_mod_cast hσ
  apply le_antisymm
  · calc
      (∫⁻ s in paymentTimes
        (ruinTime X (1 / 10 : ℝ)
          (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω) ∩
        Iic (σ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure
            (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω)) ≤
        (∫⁻ s in Icc (0 : ℝ) (u : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure
              (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω)) := by
        apply lintegral_mono_set
        intro s hs
        exact ⟨hs.1.1, le_trans hs.2 hReal⟩
      _ = 0 := hBase
  · exact bot_le
