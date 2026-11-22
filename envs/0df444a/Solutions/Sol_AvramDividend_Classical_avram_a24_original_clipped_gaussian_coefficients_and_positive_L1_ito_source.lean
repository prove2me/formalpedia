-- Prove2me | solution 1 for AvramDividend.Classical.avram_a24_original_clipped_gaussian_coefficients_and_positive_L1_ito_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T18:01:38.379959+00:00
-- url     : https://prove2.me/submissions/d5d59eef-1334-4de4-af4e-4587124ba1ee
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_canonical_gaussian_bounded_weights_integrable
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_finitecap_predictable_bounded_gaussian_coefficients_true_cash_L1
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A24 original finitecap exact Gaussian source: measurable bounded coefficients imply all physical integrability. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P) (hCashI : Integrable Cash P)
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ) (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0))) (hσle : ∀ k ω, σ k ω ≤ τ ω) (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) * w (if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P) (hν : X.ν = 0) (hFinite : C ≠ ⊤) : ∀ k,
      let S : ℕ → Finset ℕ := fun j => Finset.range (j + 1)
      let τg : ℕ → ℕ → Ω → ℝ≥0 := fun j i ω =>
        min ((i : ℝ≥0) * ((n : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0))) (σ k ω)
      let h : ℕ → ℕ → ℝ≥0 := fun j _ => (n : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)
      ∀ (hτg : ∀ j, ∀ i ∈ S j, ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τg j i ω ≤ s}),
      ∃ (G H M : ℕ → ℕ → Ω → ℝ), (∀ j i (hi : i ∈ S j),
        Measurable[(isStoppingTime_withTop_of_le_events (τg j i)
          (hτg j i hi)).measurableSpace] (G j i)) ∧ (∀ j i (hi : i ∈ S j),
        Measurable[(isStoppingTime_withTop_of_le_events (τg j i)
          (hτg j i hi)).measurableSpace] (H j i)) ∧ (∀ j, M j = fun i ω =>
        (X.X (τg j i ω + h j i) ω - ((τg j i ω + h j i) : ℝ) * X.c) -
        (X.X (τg j i ω) ω - (τg j i ω : ℝ) * X.c)) ∧
      (∀ j, ∀ i ∈ S j, Integrable (fun ω => G j i ω * M j i ω) P) ∧
      (∀ j, ∀ i ∈ S j, Integrable (H j i) P) ∧ (∀ j, ∀ i ∈ S j,
        Integrable (fun ω => H j i ω * (M j i ω)^2) P) ∧ Tendsto (fun j => ∫ ω,
        max (F k ω - w x - (∑ i ∈ S j, (G j i ω * M j i ω + (H j i ω * (M j i ω)^2 -
              (h j i : ℝ) * X.σ^2 * H j i ω)))) 0 ∂P) atTop (nhds (0 : ℝ))
:= by
  classical
  intro k
  dsimp
  intro hτg
  obtain ⟨G, H, BG, BH, hGm, hHm, hGAE, hHAE, hGB, hHB, hLim⟩ :=
    avram_a24_original_finitecap_predictable_bounded_gaussian_coefficients_true_cash_L1
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen
      hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas
      hτstop W Cash Term hW hCash hTerm hTermMeas hCashI
      σ F hσstop hσle hFsource hFI hν hFinite k hτg
  let τg : ℕ → ℕ → Ω → ℝ≥0 := fun j i ω =>
    min ((i : ℝ≥0) *
      ((n : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0))) (σ k ω)
  let h : ℕ → ℕ → ℝ≥0 := fun j _ =>
    (n : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)
  let M : ℕ → ℕ → Ω → ℝ := fun j i ω =>
    X.X (τg j i ω + h j i) ω -
      X.X (τg j i ω) ω - (h j i : ℝ) * X.c
  have hσB : ∀ ω, σ k ω ≤ (n : ℝ≥0) :=
    (avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
      X x C D hD n hn τ (σ k) hτeq (hσle k)).1
  have hInt (j i : ℕ) :=
    avram_a24_original_canonical_gaussian_bounded_weights_integrable
      X hν (σ k) (hσstop k) n hσB G H
      hGAE hHAE BG BH hGB hHB j i
  refine ⟨G, H, M, hGm, hHm, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    funext i ω
    dsimp [M, τg, h]
    push_cast
    ring
  · intro j i hi
    exact (hInt j i).1
  · intro j i hi
    exact (hInt j i).2.1
  · intro j i hi
    exact (hInt j i).2.2
  · exact hLim
