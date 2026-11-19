-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_zero_nu_topcap_masked_signed_source_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T15:23:08.622775+00:00
-- url     : https://prove2.me/submissions/25835451-8055-4b50-8bcd-d87340f8fa3d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gauss_endpoint_sigma_ne_zero_of_zero_nu_unbounded
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top12_original_zero_nu_strict_source_expected_upper_L1
import Theorems.Thm_AvramDividend_Classical_avram_b245_original_ruinclipped_allclock_inclusive_cash_terminal_to_strict_reduction
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_zero_clock_exact_physical_F_le
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
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
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
    (hFI : ∀ k, Integrable (F k) P) :
    ∀ k, ∃ Mc G R : Ω → ℝ,
      Integrable Mc P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧ (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P,
        (if σ k ω = 0 then w x else F k ω) ≤
          w x + Mc ω + G ω + R ω) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hStrict :=
    avram_ubv_top12_original_zero_nu_strict_source_expected_upper_L1
      X hX hBV (avram_gauss_endpoint_sigma_ne_zero_of_zero_nu_unbounded X hν hBV)
      hν q hq w C hC hTopCap
      hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop W Cash Term
      hW hCash hTerm hTermMeas hCashI
      σ F hσstop hσle hFsource hFI
  intro k
  let H : Ω → ℝ := fun ω =>
    if σ k ω = 0 then w x else
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
  have hh : Integrable H P ∧ (∫ ω, H ω ∂P) ≤ w x := hStrict k
  have hZero : ∀ ω : Ω, σ k ω = 0 → F k ω ≤ w x := fun ω h0 =>
    avram_ubv_loc6_original_zero_clock_exact_physical_F_le
      X x q w C D hD hjump σ F hFsource k ω h0
  have hPhys : ∀ ω, F k ω ≤ H ω := fun ω =>
    avram_b245_original_ruinclipped_allclock_inclusive_cash_terminal_to_strict_reduction
      X x C D hD w q (le_of_lt hq) hjump (σ k) (F k)
      (hFsource k) hZero ω
  have hMask : ∀ ω, (if σ k ω = 0 then w x else F k ω) ≤ H ω := by
    intro ω
    by_cases hz : σ k ω = 0
    · simp [H, hz]
    · simpa only [H, if_neg hz] using hPhys ω
  let c : ℝ := ∫ ω, H ω ∂P
  refine ⟨(fun ω => H ω - c), (fun _ => c - w x),
    (fun _ => (0 : ℝ)), hh.1.sub (integrable_const c), ?_, ?_, ?_, ?_⟩
  · rw [integral_sub hh.1 (integrable_const c)]
    simp [c]
  · exact Filter.Eventually.of_forall (fun _ => sub_nonpos.mpr hh.2)
  · exact Filter.Eventually.of_forall (fun _ => le_refl (0 : ℝ))
  · filter_upwards [Filter.Eventually.of_forall hMask] with ω hω
    change (if σ k ω = 0 then w x else F k ω) ≤
      w x + (H ω - c) + (c - w x) + 0
    linarith
