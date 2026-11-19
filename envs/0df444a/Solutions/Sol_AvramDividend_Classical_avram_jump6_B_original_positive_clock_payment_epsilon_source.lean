-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_positive_clock_payment_epsilon_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T20:21:45.589996+00:00
-- url     : https://prove2.me/submissions/d55b12b3-b408-4cd5-ad92-6beaf2076c1f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_strict_positive_clock_paymentResidual_signed_cash
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_ruin_contact_positive_clock_paymentResidual_signed_cash
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_exact_min_in_extended_time
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0)
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
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P)
    (hInfiniteActivity : X.ν (Iio (0 : ℝ)) = ⊤) : ∀ k : ℕ,
      let Cash : Ω → ℝ := fun ω : Ω =>
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
      let u : ℕ → ℕ → ℝ≥0 := fun j i =>
        (i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)
      let m : ℕ → ℕ := fun j => (n + 1) * (j + 1)
      let PaymentResidual : ℕ → Ω → ℝ := fun n ω =>
      let v : ℕ → ℝ≥0 := fun i => min (u n i) (σ k ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      let pre : Prop := σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω
      (w (x - rightLimit D 0 ω) - w x) +
        (∑ i ∈ Finset.range (m n), E (v (i + 1)) *
          (w (Y (v (i + 1))) - w (Z i))) +
        (if pre then 0 else E (σ k ω) *
          (w (riskProcess X x D (σ k ω) ω) - w (Y (σ k ω))))
      ∃ R : Ω → ℝ, Integrable R P ∧
        (∀ᵐ ω ∂P, R ω ≤ 0) ∧
        (∀ᵐ ω ∂P, σ k ω = 0 → R ω = 0) ∧
        (∀ᵐ ω ∂P, σ k ω ≠ 0 →
          ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n in atTop, PaymentResidual n ω + Cash ω ≤ R ω + ε) := by
  intro k; dsimp only
  obtain ⟨RS, hSI, hSNeg, hSZero, hSOff, hSBound⟩ :=
    avram_jump6_B_original_strict_positive_clock_paymentResidual_signed_cash
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτstop
      σ F hσstop hσle hFsource hFI hInfiniteActivity k
  obtain ⟨RR, hRI, hRNeg, hRZero, hROff, hRBound⟩ :=
    avram_jump6_B_original_ruin_contact_positive_clock_paymentResidual_signed_cash
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτstop
      σ F hσstop hσle hFsource hFI hInfiniteActivity k
  have hRuin : ∀ ω, (σ k ω : ℝ≥0∞) ≤ ruinTime X x D ω := by
    intro ω; calc
      (σ k ω : ℝ≥0∞) ≤ (τ ω : ℝ≥0∞) := by
        exact_mod_cast hσle k ω
      _ = min (ruinTime X x D ω) (n : ℝ≥0∞) :=
        avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_exact_min_in_extended_time
          X x D n τ hτeq ω
      _ ≤ ruinTime X x D ω := min_le_left _ _
  refine ⟨(fun ω => RS ω + RR ω), hSI.add hRI, ?_, ?_, ?_⟩
  · filter_upwards [hSNeg, hRNeg] with ω hs hr
    change RS ω + RR ω ≤ 0
    linarith only [hs, hr]
  · filter_upwards [hSZero, hRZero] with ω hs hr
    intro hz; change RS ω + RR ω = 0
    rw [hs hz, hr hz]; ring
  · filter_upwards [hSBound, hRBound, hSOff, hROff] with ω hs hr hso hro
    intro hz ε hε
    rcases lt_or_eq_of_le (hRuin ω) with hlt | heq
    · have hr0 : RR ω = 0 := hro (ne_of_lt hlt)
      have h := hs hz hlt ε hε; simpa only [hr0, add_zero] using h
    · have hs0 : RS ω = 0 := hso (by rw [heq]; exact lt_irrefl _)
      have h := hr hz heq ε hε; simpa only [hs0, zero_add] using h
