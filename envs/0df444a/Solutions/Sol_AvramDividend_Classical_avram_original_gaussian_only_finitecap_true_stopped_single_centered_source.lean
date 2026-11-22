-- Prove2me | solution 1 for AvramDividend.Classical.avram_original_gaussian_only_finitecap_true_stopped_single_centered_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:40:14.48051+00:00
-- url     : https://prove2.me/submissions/9fd37f4b-f733-4689-aa26-59caca78c12e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_finitecap_reward_L1_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_f6_zero_nu_finitecap_exact_clock_HJB_expected_upper
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original finite-cap Gaussian-only source reduced to the true stopped expected budget. -/
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
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P) :
    ∃ Mc : Ω → ℝ,
      Integrable Mc P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + Mc ω) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hRewardI : Integrable (fun ω => Term ω + Cash ω) P :=
    (avram_p4_f4_original_finitecap_reward_L1_nonnegative
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn
      τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm
      hTermMeas hCashI hFiniteCap).1
  have hFsource (k : ℕ) (ω : Ω) :
      Term ω + Cash ω =
        Real.exp (-(q * (τ ω : ℝ))) *
          w (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
            then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
            else riskProcess X x D (τ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal := by
    rw [hTerm ω, hCash ω, hW ω]
  have hBudget :
      (∫ ω, Term ω + Cash ω ∂P) ≤ w x := by
    have h := (avram_f6_zero_nu_finitecap_exact_clock_HJB_expected_upper
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn
      τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm
      hTermMeas hCashI
      (fun _ : ℕ => τ)
      (fun (_ : ℕ) (ω : Ω) => Term ω + Cash ω)
      (fun _ => hτstop) (fun _ _ => le_rfl)
      hFsource (fun _ => hRewardI) hν hFiniteCap) 0
    exact h
  let m : ℝ := ∫ ω, Term ω + Cash ω ∂P
  let M : Ω → ℝ := fun ω => Term ω + Cash ω - m
  have hMI : Integrable M P := hRewardI.sub (integrable_const m)
  have hM0 : (∫ ω, M ω ∂P) = 0 := by
    change (∫ ω, (Term ω + Cash ω) - m ∂P) = 0
    rw [integral_sub hRewardI (integrable_const m)]
    simp [m]
  refine ⟨M, hMI, hM0, Filter.Eventually.of_forall (fun ω => ?_)⟩
  dsimp [M, m]
  linarith
