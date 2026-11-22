-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_original_finiteactivity_finitecap_trueclock_discounted_G_Jsmall_fullreward_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T23:07:49.590449+00:00
-- url     : https://prove2.me/submissions/b73aa7d0-6bdc-4196-923b-1a56fdd79f7d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_jump6_finiteactivity_true_ruinclipped_terminal_original_continuous_G_and_centered_Jsmall
import Theorems.Thm_AvramDividend_Classical_avram_jump6_original_allnu_finitecap_canonical_stopped_full_reward_L1
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact original finite-cap true-clock discounted terminal and inclusive
cash through the continuous Gaussian and initially centred smallmark channels. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (x : ℝ) (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
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
    ∃ (G Jsmall : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => G t ω)) ∧
      (∀ t : ℝ≥0, Integrable (G t) P ∧ (∫ ω, G t ω ∂P) = 0) ∧
      Integrable (fun ω => Jsmall (τ ω) ω) P ∧
      (∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P
        (fun η => Jsmall (τ η) η) ω = 0) ∧
      AEStronglyMeasurable Term P ∧ Integrable Cash P ∧
      Integrable (fun ω => Term ω + Cash ω) P ∧
      MeasurableSet[𝓕.rightCont 0] {ω : Ω | τ ω ≠ 0} ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω =
        Real.exp (-(q * (τ ω : ℝ))) *
          w (x + (τ ω : ℝ) * X.c +
            G (τ ω) ω + Jsmall (τ ω) ω +
            avram_p4_h_gaussian_intrinsic_large_jump_sum X (τ ω) ω -
            (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
             then rightLimit D (τ ω) ω else D (τ ω) ω)) + Cash ω) := by
  obtain ⟨G, Jsmall, _hAdapt, _hZero, hGcont, hGcenter, _hGmart,
      _hJfixedI, hJstopI, hJinitial, hWsource⟩ :=
    avram_jump6_finiteactivity_true_ruinclipped_terminal_original_continuous_G_and_centered_Jsmall
      X hX hFinite x D n hn τ hτeq hτstop W hW
  obtain ⟨hTermMeas, hCashI, _hTermI, hFullI, hEvent⟩ :=
    avram_jump6_original_allnu_finitecap_canonical_stopped_full_reward_L1
      X x C hCfinite hxc w hw_cont hw_neg D hD
      q (le_of_lt hq) n τ hτeq hτmeas hτstop
      W Cash Term hW hCash hTerm
  have hExact : ∀ᵐ ω ∂P, Term ω + Cash ω =
      Real.exp (-(q * (τ ω : ℝ))) *
        w (x + (τ ω : ℝ) * X.c +
          G (τ ω) ω + Jsmall (τ ω) ω +
          avram_p4_h_gaussian_intrinsic_large_jump_sum X (τ ω) ω -
          (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
           then rightLimit D (τ ω) ω else D (τ ω) ω)) + Cash ω := by
    filter_upwards [hWsource] with ω hw
    calc
      Term ω + Cash ω =
          Real.exp (-(q * (τ ω : ℝ))) * w (W ω) + Cash ω := by
        rw [hTerm ω]
      _ = _ := by rw [hw]
  exact ⟨G, Jsmall, hGcont, hGcenter, hJstopI, hJinitial,
    hTermMeas, hCashI, hFullI, hEvent, hExact⟩

