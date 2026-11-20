-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_actual_positive_event_first_mark_cash_ruin_excludes_unit_fullmark_ledger
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T13:02:07.899779+00:00
-- url     : https://prove2.me/submissions/6b50019e-b6ca-425c-8800-936f2badd2fe

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_first_size2_ruin_cash_excludes_physical_unitmark_certificate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (A : Set Ω) (hA : 0 < P A)
    (B : Ω → ℝ≥0 → ℝ) (N : Ω → ℝ≥0 → ℕ)
    (σ u : Ω → ℝ≥0) (q : ℝ) (Drift : Ω → ℝ)
    (hData : ∀ᵐ ω ∂(P.restrict A),
      (∀ t : ℝ≥0, X.X t ω = B ω t - 2 * (N ω t : ℝ)) ∧
      (∀ t : ℝ≥0, t ≤ σ ω → |B ω t| < (1 / 4000 : ℝ)) ∧
      (∀ t : ℝ≥0, t < σ ω → N ω t = 0) ∧
      (N ω (σ ω) = 1) ∧
      ((u ω : ℝ≥0∞) =
        (⨅ (s : ℝ≥0)
          (_ : (1 / 5 : ℝ) - (1 / 10 : ℝ) < X.X s ω),
          (s : ℝ≥0∞))) ∧
      ((σ ω : ℝ) ≤ 1 / 10) ∧ Drift ω ≤ 0)
    (hLedger : ∀ᵐ ω ∂(P.restrict A),
      Real.exp (-(q * (σ ω : ℝ))) *
        (if riskProcess X (1 / 10 : ℝ)
            (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ))
            (σ ω) ω < 0 then 0
         else 1 + riskProcess X (1 / 10 : ℝ)
            (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ))
            (σ ω) ω +
            (riskProcess X (1 / 10 : ℝ)
              (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ))
              (σ ω) ω) ^ 2) +
        (∫⁻ s in paymentTimes
            (ruinTime X (1 / 10 : ℝ)
              (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω)
            ∩ Iic (σ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure
              (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω)).toReal ≤
      (1 + (1 / 10 : ℝ) + (1 / 10 : ℝ) ^ 2) +
      B ω (σ ω) + (-2 * (N ω (σ ω) : ℝ) + 2 * (σ ω : ℝ)) +
      Drift ω) :
    False := by
  have hNonzero : P.restrict A ≠ 0 := by
    intro hzero
    have hz : (P.restrict A) Set.univ = 0 := by
      simp [hzero]
    exact (ne_of_gt hA) (by simpa using hz)
  haveI : (ae (P.restrict A)).NeBot := ae_neBot.mpr hNonzero
  have hAll : ∀ᵐ ω ∂(P.restrict A),
      ((∀ t : ℝ≥0, X.X t ω = B ω t - 2 * (N ω t : ℝ)) ∧
      (∀ t : ℝ≥0, t ≤ σ ω → |B ω t| < (1 / 4000 : ℝ)) ∧
      (∀ t : ℝ≥0, t < σ ω → N ω t = 0) ∧
      (N ω (σ ω) = 1) ∧
      ((u ω : ℝ≥0∞) =
        (⨅ (s : ℝ≥0)
          (_ : (1 / 5 : ℝ) - (1 / 10 : ℝ) < X.X s ω),
          (s : ℝ≥0∞))) ∧
      ((σ ω : ℝ) ≤ 1 / 10) ∧ Drift ω ≤ 0) ∧
      (Real.exp (-(q * (σ ω : ℝ))) *
        (if riskProcess X (1 / 10 : ℝ)
            (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ))
            (σ ω) ω < 0 then 0
         else 1 + riskProcess X (1 / 10 : ℝ)
            (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ))
            (σ ω) ω +
            (riskProcess X (1 / 10 : ℝ)
              (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ))
              (σ ω) ω) ^ 2) +
        (∫⁻ s in paymentTimes
            (ruinTime X (1 / 10 : ℝ)
              (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω)
            ∩ Iic (σ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure
              (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω)).toReal ≤
      (1 + (1 / 10 : ℝ) + (1 / 10 : ℝ) ^ 2) +
      B ω (σ ω) + (-2 * (N ω (σ ω) : ℝ) + 2 * (σ ω : ℝ)) +
      Drift ω) := by
    filter_upwards [hData, hLedger] with ω hd hl
    exact ⟨hd, hl⟩
  obtain ⟨ω, ⟨⟨hp, ht, hb, hn, hu, hs, hd⟩, hL⟩⟩ := hAll.exists
  let w : ℝ → ℝ := fun z =>
    if z < 0 then 0 else 1 + z + z ^ 2
  exact avram_jump6_A_actual_first_size2_ruin_cash_excludes_physical_unitmark_certificate
    X ω (B ω) (N ω) (σ ω) (u ω) hp ht hb hn hu hs q w
    (by intro z; rfl)
    (Real.exp (-(q * (σ ω : ℝ))) *
      w (riskProcess X (1 / 10 : ℝ)
        (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ))
        (σ ω) ω) +
      (∫⁻ s in paymentTimes
          (ruinTime X (1 / 10 : ℝ)
            (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω)
          ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure
            (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω)).toReal)
    (-2 * (N ω (σ ω) : ℝ) + 2 * (σ ω : ℝ))
    (Drift ω) rfl rfl hd (by
      rw [show w (1 / 10 : ℝ) =
          (1 + (1 / 10 : ℝ) + (1 / 10 : ℝ) ^ 2) by
            norm_num [w]]
      exact hL)
