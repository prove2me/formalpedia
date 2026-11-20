-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_positive_expected_budget_topcap
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:35:49.411719+00:00
-- url     : https://prove2.me/submissions/2b794a8f-cc4c-4b47-81fe-18fb6baa6c2f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_physical_five_signed_ito_components
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_supported_mean_zero_event_budget
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
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
    (hInfiniteActivity : X.ν (Iio (0 : ℝ)) = ⊤)
    (hCapCase : C = ⊤) :
    ∀ k, (∫ ω in {ω : Ω | σ k ω ≠ 0}, F k ω ∂P) ≤
      w x * (P {ω : Ω | σ k ω ≠ 0}).toReal := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k
  obtain ⟨Mc, Ms, Ml, G, R, hMcI, hMsI, hMlI,
      hMc0, hMs0, hMl0, hMcOff, hMsOff, hMlOff,
      hG, hR, hBound⟩ :=
    avram_mix_inf20_original_physical_five_signed_ito_components
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτstop σ F hσstop hσle hFsource hFI
      hInfiniteActivity k
  let A : Set Ω := {ω | σ k ω ≠ 0}
  have hA : MeasurableSet A := by
    have hZero := avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
      𝓕 (σ k) (hσstop k)
    change MeasurableSet ({ω : Ω | σ k ω = 0}ᶜ)
    exact hZero.compl
  let M : Ω → ℝ := fun ω => Mc ω + Ms ω + Ml ω
  have hMI : Integrable M P := (hMcI.add hMsI).add hMlI
  have hMzero : (∫ ω, M ω ∂P) = 0 := by
    have hSum : (∫ ω, Mc ω + Ms ω + Ml ω ∂P) =
        (∫ ω, Mc ω ∂P) + (∫ ω, Ms ω ∂P) + (∫ ω, Ml ω ∂P) := by
      calc
        (∫ ω, Mc ω + Ms ω + Ml ω ∂P) =
            (∫ ω, Mc ω + Ms ω ∂P) + (∫ ω, Ml ω ∂P) := by
              simpa only [Pi.add_apply] using integral_add (hMcI.add hMsI) hMlI
        _ = _ := by rw [integral_add hMcI hMsI]
    change (∫ ω, Mc ω + Ms ω + Ml ω ∂P) = 0
    rw [hSum, hMc0, hMs0, hMl0]
    norm_num
  have hMoff : ∀ᵐ ω ∂P, ω ∉ A → M ω = 0 := by
    filter_upwards [hMcOff, hMsOff, hMlOff] with ω hc hs hl
    intro hNotA
    have hZero : σ k ω = 0 := by simpa [A] using hNotA
    simp [M, hc hZero, hs hZero, hl hZero]
  have hUpper : ∀ᵐ ω ∂P, F k ω ≤ w x + M ω := by
    filter_upwards [hG, hR, hBound] with ω hg hr hb
    dsimp [M]
    linarith
  exact avram_mix_inf15_supported_mean_zero_event_budget
    A hA (w x) (F k) M (hFI k) hMI hMzero hMoff hUpper
