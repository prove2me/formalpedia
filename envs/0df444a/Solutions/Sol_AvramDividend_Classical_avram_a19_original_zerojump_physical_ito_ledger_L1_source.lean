-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_original_zerojump_physical_ito_ledger_L1_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:21:37.90088+00:00
-- url     : https://prove2.me/submissions/21b82ddf-f9e8-48c0-874f-5fd95f5df6f9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_finitecap_gaussian_physical_stopped_mesh_ito_positive_error
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
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
    ∀ k, ∃
      (S : ℕ → Finset ℕ) (τg : ℕ → ℕ → Ω → ℝ≥0)
      (B h : ℕ → ℕ → ℝ≥0)
      (G H M : ℕ → ℕ → Ω → ℝ)
      (L : Ω → ℝ)
      (hτg : ∀ j, ∀ i ∈ S j, ∀ s : ℝ≥0,
        MeasurableSet[𝓕.rightCont s] {ω : Ω | τg j i ω ≤ s}),
      (𝓕.rightCont 0 ≤ mΩ) ∧
      (∀ j, ∀ i ∈ S j, ∀ ω, τg j i ω ≤ B j i) ∧
      (∀ j i (hi : i ∈ S j),
        Measurable[(isStoppingTime_withTop_of_le_events
          (τg j i) (hτg j i hi)).measurableSpace] (G j i)) ∧
      (∀ j i (hi : i ∈ S j),
        Measurable[(isStoppingTime_withTop_of_le_events
          (τg j i) (hτg j i hi)).measurableSpace] (H j i)) ∧
      (∀ j, M j = fun i ω =>
        (X.X (τg j i ω + h j i) ω -
          ((τg j i ω + h j i) : ℝ) * X.c) -
        (X.X (τg j i ω) ω - (τg j i ω : ℝ) * X.c)) ∧
      (∀ j, ∀ i ∈ S j,
        Integrable (fun ω => G j i ω * M j i ω) P) ∧
      (∀ j, ∀ i ∈ S j, Integrable (H j i) P) ∧
      (∀ j, ∀ i ∈ S j,
        Integrable (fun ω => H j i ω * (M j i ω) ^ 2) P) ∧
      Integrable L P ∧
      Tendsto (fun j => eLpNorm (fun ω =>
        L ω - ∑ i ∈ S j,
          (G j i ω * M j i ω +
            (H j i ω * M j i ω ^ 2 -
              ((h j i : ℝ) * X.σ ^ 2) * H j i ω))) 1 P)
        atTop (nhds 0) ∧
      (∀ᵐ ω ∂P, F k ω ≤ w x + L ω)  := by
  intro k
  obtain ⟨S, τg, B, h, G, H, M, L, E, hτg,
    hF0, hB, hG, hH, hM, hGI, hHI, hH2I,
    hLI, hL1, hQconv, hEconv, hCash⟩ :=
    avram_a20_original_finitecap_gaussian_physical_stopped_mesh_ito_positive_error
      X hX hBV hν q hq w C hC hFiniteCap
      hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump n hn
      τ hτeq hτmeas hτstop σ F hσstop hσle hFsource hFI k
  refine ⟨S, τg, B, h, G, H, M, L, hτg,
    hF0, hB, hG, hH, hM, hGI, hHI, hH2I,
    hLI, hL1, ?_⟩
  filter_upwards [hQconv, hEconv, hCash] with ω hQω hEω hCashω
  have hLimit : Tendsto
      (fun j => w x + (∑ i ∈ S j,
      (G j i ω * M j i ω +
        (H j i ω * M j i ω ^ 2 -
          ((h j i : ℝ) * X.σ ^ 2) * H j i ω))) + E j ω)
      atTop (nhds (w x + L ω)) := by
    simpa only [add_zero] using
      ((tendsto_const_nhds.add hQω).add hEω)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hLimit
    (Filter.Eventually.of_forall (fun j => hCashω j))
