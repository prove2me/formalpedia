-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_finitecap_original_stopped_reward_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T18:27:13.949452+00:00
-- url     : https://prove2.me/submissions/6361260e-7267-4d88-957a-55e7b83e64e0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin36_original_finitecap_any_stopped_full_reward_L1
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original ruin-clipped finite-cap post-dividend reward is L1,
including its exact physical dividend Stieltjes cash integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hFiniteCap : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    Integrable (fun ω => Term ω + Cash ω) P := by
  have hBound : ∀ ω, τ ω ≤ (n : ℝ≥0) :=
    (avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
      X x C D hD n hn τ τ hτeq (fun ω => le_refl (τ ω))).1
  have hFull : ∀ ω,
      Term ω + Cash ω =
      Real.exp (-(q * (τ ω : ℝ))) *
        w (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
          else riskProcess X x D (τ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal := by
    intro ω
    rw [hTerm ω, hCash ω, hW ω]
  exact avram_mix_fin36_original_finitecap_any_stopped_full_reward_L1
    X x q hq w hw_cont hw_neg C hFiniteCap hxc D hD
    n τ hτstop hBound (fun ω => Term ω + Cash ω) hFull

