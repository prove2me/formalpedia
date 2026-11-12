-- Prove2me | solution 1 for AvramDividend.Classical.avram_jb23_original_compact_reward_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:26:04.231738+00:00
-- url     : https://prove2.me/submissions/16c91bb7-dea2-4d45-9669-5c437ec48a4b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin36_original_finitecap_any_stopped_full_reward_L1
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Indexing a bounded original stopped reward preserves L1 integrability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (κ : ℕ → Ω → ℝ≥0)
    (hκstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (κ k ω : WithTop ℝ≥0)))
    (hκbound : ∀ k ω, κ k ω ≤ (n : ℝ≥0))
    (H : ℕ → Ω → ℝ)
    (hHsource : ∀ k ω, H k ω =
      Real.exp (-(q * (κ k ω : ℝ))) *
        w (if κ k ω = 0 ∨
              (κ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (κ k ω) ω - rightLimit D (κ k ω) ω
          else riskProcess X x D (κ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) :
    ∀ k, Integrable (H k) P := by
  intro k
  exact avram_mix_fin36_original_finitecap_any_stopped_full_reward_L1
    X x q hq w hw_cont hw_neg C hCfinite hxc D hD n
    (κ k) (hκstop k) (hκbound k) (H k) (hHsource k)
