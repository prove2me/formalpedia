-- Prove2me | solution 2 for AvramDividend.Classical.avram_f7_original_any_compact_clock_ito_signed_source_witnesses
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T08:06:05.159988+00:00
-- url     : https://prove2.me/submissions/844df9fb-0a02-4843-801c-dc51b5c1b45c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_localised_nonzero_nu_signed_residual
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_localised_zero_nu_signed_residual
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hStop : (∀ k, IsStoppingTime 𝓕.rightCont
        (fun ω => (σ k ω : WithTop ℝ≥0))))
    (hBound : (∀ k ω, σ k ω ≤ τ ω))
    (hExact : (∀ k ω, F k ω =
        Real.exp (-(q * (σ k ω : ℝ))) *
          w (if σ k ω = 0 ∨
                (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
              x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
            else riskProcess X x D (σ k ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal))
    (hMeas : (∀ k, Measurable (F k)))
    (hInt : (∀ k, Integrable (F k) P))
    (hNonneg : (∀ k, 0 ≤ᵐ[P] F k)) :
    ∀ k : ℕ, ∃ M G H : Ω → ℝ,
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, F k ω ≤ w x + M ω + G ω + H ω) := by
  letI : IsProbabilityMeasure P := X.isProbability
  classical
  have hLift (M : ℕ → Ω → ℝ)
      (hMI : ∀ k, Integrable (M k) P)
      (hMn : ∀ k, (∫ ω, M k ω ∂P) ≤ 0)
      (hMB : ∀ k, ∀ᵐ ω ∂P, F k ω ≤ w x + M k ω) :
      ∀ k, ∃ Mc G H : Ω → ℝ,
        Integrable Mc P ∧ Integrable G P ∧ Integrable H P ∧
        (∫ ω, Mc ω ∂P) = 0 ∧
        (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
        (∀ᵐ ω ∂P, F k ω ≤ w x + Mc ω + G ω + H ω) := by
    intro k
    let a : ℝ := ∫ ω, M k ω ∂P
    let Mc : Ω → ℝ := fun ω => M k ω - a
    let G : Ω → ℝ := fun _ => a
    let H : Ω → ℝ := fun _ => 0
    refine ⟨Mc, G, H, (hMI k).sub (integrable_const a),
      integrable_const a, integrable_const 0, ?_, ?_, ?_⟩
    · change (∫ ω, M k ω - a ∂P) = 0
      rw [integral_sub (hMI k) (integrable_const a)]
      simp [a]
    · filter_upwards [] with ω
      change a + 0 ≤ 0
      simpa [a] using hMn k
    · filter_upwards [hMB k] with ω hω
      change F k ω ≤ w x + (M k ω - a) + a + 0
      linarith
  by_cases hν : X.ν = 0
  · obtain ⟨M, hMI, hMn, hMB⟩ :=
      avram_p4_f6_localised_zero_nu_signed_residual
        X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen
        hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas
        hτstop W Cash Term hW hCash hTerm hTermMeas hCashI
        σ F hStop hBound hExact hInt hν
    exact hLift M hMI hMn hMB
  · obtain ⟨M, hMI, hMn, hMB⟩ :=
      avram_p4_f6_localised_nonzero_nu_signed_residual
        X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen
        hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas
        hτstop W Cash Term hW hCash hTerm hTermMeas hCashI
        σ F hStop hBound hExact hInt hν
    exact hLift M hMI hMn hMB
