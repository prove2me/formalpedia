-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_mixed12_finite_activity_source_martingale_majorant
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T14:16:48.096316+00:00
-- url     : https://prove2.me/submissions/1bb7ce2e-f9e3-4e6c-8fdf-0ef474a36abe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a07_finite_source_initial_condexp_upper

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
    (n : ℕ) (hn : 0 < n)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
              (σ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : Integrable F P)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ M : Ω → ℝ, Integrable M P ∧
      (∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P M ω = 0) ∧
      (∀ᵐ ω ∂P, F ω ≤ w x + M ω) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let G : Ω → ℝ := condExp (𝓕.rightCont 0) P F
  let M : Ω → ℝ := fun ω => F ω - G ω
  have hGI : Integrable G P := integrable_condExp
  have hMI : Integrable M P := hFI.sub hGI
  have hIdem :=
    condExp_condExp_of_le (le_refl (𝓕.rightCont 0))
      (𝓕.rightCont.le 0) (μ := P) (f := F)
  have hZero : ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont 0) P M ω = 0 := by
    filter_upwards [condExp_sub hFI hGI (𝓕.rightCont 0), hIdem]
      with ω hs hi
    change condExp (𝓕.rightCont 0) P (F - G) ω = 0
    rw [hs]
    change condExp (𝓕.rightCont 0) P F ω -
      condExp (𝓕.rightCont 0) P (condExp (𝓕.rightCont 0) P F) ω = 0
    rw [hi]
    ring
  have hBudget :=
    avram_a07_finite_source_initial_condexp_upper
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn σ hσstop hσbound F hFsource hFI hFiniteActivity
  have hUpper : ∀ᵐ ω ∂P, F ω ≤ w x + M ω := by
    filter_upwards [hBudget] with ω hb
    change F ω ≤ w x + (F ω - condExp (𝓕.rightCont 0) P F ω)
    linarith
  exact ⟨M, hMI, hZero, hUpper⟩
