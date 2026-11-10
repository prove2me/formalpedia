-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin18_original_bounded_clock_cofinal_full_reward_eventually_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T01:19:24.901192+00:00
-- url     : https://prove2.me/submissions/fc9326a8-8628-4900-8f06-bd5fc819a778

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (σ : Ω → ℝ≥0)
    (hσbound : ∀ ω, (σ ω : ℝ≥0∞) ≤ (n : ℝ≥0∞))
    (S : ℕ → Ω → ℝ≥0∞)
    (hSmono : ∀ ω, Monotone (fun k => S k ω))
    (hSsup : ∀ᵐ ω ∂P, (⨆ k : ℕ, S k ω) = ⊤)
    (σk : ℕ → Ω → ℝ≥0)
    (hσk : ∀ k ω, σk k ω = (min (σ ω : ℝ≥0∞) (S k ω)).toNNReal)
    (F : Ω → ℝ) (Fk : ℕ → Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
              (σ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFksource : ∀ k ω, Fk k ω =
      Real.exp (-(q * (σk k ω : ℝ))) *
        w (if σk k ω = 0 ∨
              (σk k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σk k ω) ω - rightLimit D (σk k ω) ω
          else riskProcess X x D (σk k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σk k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) :
    ∀ᵐ ω ∂P, ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      σk k ω = σ ω ∧ Fk k ω = F ω := by
  filter_upwards [hSsup] with ω hω
  have hlt : (n : ℝ≥0∞) < (⨆ k : ℕ, S k ω) := by
    rw [hω]
    simp
  obtain ⟨K, hK⟩ := lt_iSup_iff.mp hlt
  refine ⟨K, ?_⟩
  intro k hk
  have hbound : (σ ω : ℝ≥0∞) ≤ S k ω :=
    (hσbound ω).trans ((le_of_lt hK).trans (hSmono ω hk))
  have hclock : σk k ω = σ ω := by
    rw [hσk k ω, min_eq_left hbound]
    simp
  refine ⟨hclock, ?_⟩
  rw [hFksource k ω, hFsource ω, hclock]
