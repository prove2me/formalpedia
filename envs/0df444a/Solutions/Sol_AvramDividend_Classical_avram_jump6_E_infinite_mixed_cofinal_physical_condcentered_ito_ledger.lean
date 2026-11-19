-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_E_infinite_mixed_cofinal_physical_condcentered_ito_ledger
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T23:16:15.782727+00:00
-- url     : https://prove2.me/submissions/a1ead72d-09e0-411a-a1d8-ce280a0d1521
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

import Theorems.Thm_AvramDividend_Classical_avram_jump6_E_infinite_original_single_clock_physical_signed_source
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q)
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
    (hTermMeas : AEStronglyMeasurable Term P) (hCashI : Integrable Cash P)
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
    (hTop : C = ⊤) (hInfinite : X.ν (Iio (0 : ℝ)) = ⊤) :
    ∀ i : ℕ,
    ∃ (S : ℕ → Ω → ℝ≥0∞) (ρ : ℕ → Ω → ℝ≥0)
      (Q : ℕ → Ω → ℝ),
      (∀ ω, Monotone (fun j => S j ω)) ∧
      (∀ᵐ ω ∂P, (⨆ j : ℕ, S j ω) = ⊤) ∧
      (∀ j ω, ρ j ω = (min (σ i ω : ℝ≥0∞) (S j ω)).toNNReal) ∧
      Measurable (σ i) ∧
      (∀ j, Measurable (ρ j)) ∧
      (∀ j ω, ρ j ω ≤ σ i ω) ∧
      (∀ j, IsStoppingTime 𝓕.rightCont
        (fun ω => (ρ j ω : WithTop ℝ≥0))) ∧
      (∀ j ω, Q j ω =
        Real.exp (-(q * (ρ j ω : ℝ))) *
          w (if ρ j ω = 0 ∨
                (ρ j ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (ρ j ω) ω - rightLimit D (ρ j ω) ω
          else riskProcess X x D (ρ j ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ j ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) ∧
      (∀ j, Measurable (Q j)) ∧
      (∀ j, Integrable (Q j) P) ∧
      (∀ j, ∃ M G R : Ω → ℝ, Integrable M P ∧
        (∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P M ω = 0) ∧
        (∀ᵐ ω ∂P, G ω ≤ 0) ∧
        (∀ᵐ ω ∂P, R ω ≤ 0) ∧
        (∀ᵐ ω ∂P, Q j ω ≤ w x + M ω + G ω + R ω)) := by
  classical
  intro i
  obtain ⟨hσmeas, hFmeas, M, G, R, hMI, hM0, hG, hR, hUpper⟩ :=
    avram_jump6_E_infinite_original_single_clock_physical_signed_source
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop W Cash Term
      hW hCash hTerm hTermMeas hCashI σ F
      hσstop hσle hFsource hFI hTop hInfinite i
  let S : ℕ → Ω → ℝ≥0∞ := fun _ _ => ⊤
  let ρ : ℕ → Ω → ℝ≥0 := fun _ ω => σ i ω
  let Q : ℕ → Ω → ℝ := fun _ ω => F i ω
  refine ⟨S, ρ, Q, ?_, ?_, ?_, hσmeas, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω j k hjk; exact le_rfl
  · exact Filter.Eventually.of_forall (fun ω => by simp [S])
  · intro j ω; simp [S, ρ]
  · intro j; simpa [ρ] using hσmeas
  · intro j ω; exact le_rfl
  · intro j; simpa [ρ] using (hσstop i)
  · intro j ω; simpa only [Q, ρ] using (hFsource i ω)
  · intro j; simpa [Q] using hFmeas
  · intro j; simpa [Q] using (hFI i)
  · intro j; exact ⟨M, G, R, hMI, hM0, hG, hR, by simpa [Q] using hUpper⟩
