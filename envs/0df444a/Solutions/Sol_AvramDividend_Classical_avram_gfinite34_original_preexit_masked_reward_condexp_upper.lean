-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite34_original_preexit_masked_reward_condexp_upper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T10:15:08.108657+00:00
-- url     : https://prove2.me/submissions/d460fc28-9635-448f-82f7-9a93693747b2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gfinite35_original_preexit_masked_reward_initial_event_budget
import Theorems.Thm_AvramDividend_Classical_avram_gfinite28_original_bounded_stop_masked_strict_reward_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite14_initial_event_budget_to_condexp
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
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
    (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k (ρ : Ω → ℝ≥0)
      (hρstop : IsStoppingTime 𝓕.rightCont
        (fun ω => (ρ ω : WithTop ℝ≥0)))
      (hρle : ∀ ω, ρ ω ≤ σ k ω)
      (δ : ℝ) (hδ : 0 < δ)
      (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
        δ ≤ riskProcess X x D t ω),
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont 0) P (fun η =>
          if ρ η = 0 then w x else
            Real.exp (-(q * (ρ η : ℝ))) *
              w (riskProcess X x D (ρ η) η) +
            (∫⁻ s in paymentTimes (ruinTime X x D η) ∩ Iio (ρ η : ℝ),
              ENNReal.ofReal (Real.exp (-(q * s)))
              ∂(dividendMeasure D η)).toReal) ω ≤ w x := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k ρ hρstop hρle δ hδ hFloor
  let F : Ω → ℝ := fun ω =>
    if ρ ω = 0 then w x else
      Real.exp (-(q * (ρ ω : ℝ))) *
        w (riskProcess X x D (ρ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal
  have hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0) := by
    intro ω
    calc
      ρ ω ≤ σ k ω := hρle ω
      _ ≤ τ ω := hσle k ω
      _ ≤ (n : ℝ≥0) := by
        rw [hτeq ω]
        exact (avram_wave7_08_source_truncated_clock_nnreal_bounds X x D n).2.1 ω
  have hFI : Integrable F P := by
    exact avram_gfinite28_original_bounded_stop_masked_strict_reward_L1
      X x C hFiniteCap hxc D hD w hw_cont hw_neg q hq
      ρ hρstop (n : ℝ≥0) hρbound
  have hBudget (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A) :
      (∫ ω in A, F ω ∂P) ≤ w x * (P A).toReal := by
    exact avram_gfinite35_original_preexit_masked_reward_initial_event_budget
      X hX hBV hν q hq w C hC hFiniteCap
      hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop σ hσstop hσle
      k ρ hρstop hρle δ hδ hFloor A hA
  exact avram_ubv_finite14_initial_event_budget_to_condexp
    F (w x) hFI hBudget
