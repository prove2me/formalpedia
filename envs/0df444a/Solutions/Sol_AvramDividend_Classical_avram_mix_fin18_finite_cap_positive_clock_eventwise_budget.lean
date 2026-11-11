-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin18_finite_cap_positive_clock_eventwise_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T08:32:17.097198+00:00
-- url     : https://prove2.me/submissions/edec986d-a730-414b-91bf-8c555ed6b0bb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin20_original_finite_spatial_local_ito_budget
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin19_original_spatial_reward_eventwise_fatou_from_exact_cofinal
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_any_clock_exact_closed_payoff_nonnegative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original finite mixed physical cash inequality from compact stopped Ito budgets. -/
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
    (hσclip : ∀ ω, σ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
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
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hCfinite : C ≠ ⊤) :
    ∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
      (∫ ω in A ∩ {ω : Ω | σ ω ≠ 0}, F ω ∂P) ≤
        w x * (P (A ∩ {ω : Ω | σ ω ≠ 0})).toReal := by
  intro A hA
  obtain ⟨S, σk, Fk, b, hAmeas, hSmono, hSsup, hσk,
    hσmeas, hσkmeas, hσkle, hσkstop, hFksource,
    hFkmeas, hFkint, hb, hbBound, hBudget⟩ :=
    avram_mix_fin20_original_finite_spatial_local_ito_budget
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg
      hjump n hn σ hσstop hσbound hσclip F hFsource
      hFI hFiniteActivity hCfinite A hA
  have hσbound' : ∀ ω, (σ ω : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
    intro ω
    exact ENNReal.coe_le_coe.mpr (hσbound ω)
  have hFnonneg : ∀ ω, 0 ≤ F ω :=
    avram_ubv_loc6_original_any_clock_exact_closed_payoff_nonnegative
      X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hxc D hD q σ F hFsource
  have hFkpos : ∀ k ω, σk k ω ≠ 0 → 0 ≤ Fk k ω := by
    intro k ω _
    exact avram_ubv_loc6_original_any_clock_exact_closed_payoff_nonnegative
      X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hxc D hD q (σk k) (Fk k) (hFksource k) ω
  have hExpected :=
    avram_mix_fin19_original_spatial_reward_eventwise_fatou_from_exact_cofinal
      X x q w D n σ hσbound' S hSmono hSsup
      σk hσk F Fk hFsource hFksource hσmeas
      hσkmeas hσkle hFI.aestronglyMeasurable hFkmeas
      hFkint (by intro ω _; exact hFnonneg ω) hFkpos
      A hAmeas b hb hBudget
  exact le_trans hExpected hbBound
