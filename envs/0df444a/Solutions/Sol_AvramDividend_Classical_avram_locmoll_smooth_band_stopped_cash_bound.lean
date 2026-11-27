-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_smooth_band_stopped_cash_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:55:52.85011+00:00
-- url     : https://prove2.me/submissions/819f9343-4c69-42c1-a8d3-f9cf9603c2c8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_physical_ito_ledger
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_generator_drift_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_random_closed_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerF_signed_centered_upper_to_ennreal_budget
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (C : ℝ≥0∞) (hC : 0 < C)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T)
    (δ R : ℝ) (hδ : 0 < δ) (hδx : δ < x) (hxR : x < R)
    (θ : Ω → ℝ≥0)
    (hθle : ∀ ω, θ ω ≤ T.toNNReal)
    (hprefix : ∀ ω t, t < θ ω →
      x + X.X t ω - rightLimit D t ω ∈ Icc δ R)
    (hstop : IsStoppingTime 𝓕.rightCont (fun ω => (θ ω : WithTop ℝ≥0)))
    (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (hNonneg : ∀ y : ℝ, 0 ≤ g y)
    (hZero : ∀ y : ℝ, y ≤ 0 → g y = 0)
    (hGrad : ∀ y : ℝ, δ ≤ y → 1 ≤ deriv g y)
    (hGen : ∀ y : ℝ, δ ≤ y → ENNReal.ofReal y ≤ C →
      X.GeneratorIntegrable g y ∧ X.generator g y - q * g y ≤ 0)
    (hSec : ∀ a b : ℝ, δ ≤ b → b ≤ a →
      a - b ≤ g a - g b)
    (hLoss : ∀ a b : ℝ, 0 ≤ b → b ≤ a →
      a - b ≤ g a - g b + δ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (θ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (g x + δ) := by 
  letI : IsProbabilityMeasure P := X.isProbability
  let F : Ω → ℝ≥0∞ := fun ω => ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (θ ω : ℝ),
    ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  let G : Ω → ℝ := (fun ω : Ω => ∫ t in Ioc (0 : ℝ) (θ ω : ℝ),
      Real.exp (-(q * t)) *
        (X.generator g (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t.toNNReal) -
          q * g (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t.toNNReal)))
  obtain ⟨M, hMI, hM0, hIto⟩ := avram_locmoll_band_physical_ito_ledger X hX hBV q hq C hC x hx hxc D hD T hT δ R hδ hδx hxR θ hθle hprefix hstop g hg hNonneg hZero hGrad hGen hSec hLoss
  have hF : AEMeasurable F P :=
    avram_locmoll_random_closed_cash_measurable X x D hD.1.1 q θ hstop
  have hG : ∀ᵐ ω ∂P, G ω ≤ 0 := Filter.Eventually.of_forall
    (avram_locmoll_band_generator_drift_nonpositive X hX hBV q hq C hC x hx hxc D hD T hT δ R hδ hδx hxR θ hθle hprefix hstop g hg hNonneg hZero hGrad hGen hSec hLoss)
  have hBudget : ∀ᵐ ω ∂P, (F ω).toReal ≤ g x + δ + M ω + G ω + 0 := by
    filter_upwards [hIto] with ω hω
    have hterm : 0 ≤ Real.exp (-(q * (θ ω : ℝ))) *
      g (if θ ω = 0 ∨ (θ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (θ ω) ω - rightLimit D (θ ω) ω
        else riskProcess X x D (θ ω) ω) :=
      mul_nonneg (Real.exp_pos _).le (hNonneg _)
    change _ + (F ω).toReal ≤ g x + δ + M ω + G ω at hω
    linarith
  have hb := avram_pj_workerF_signed_centered_upper_to_ennreal_budget
    (fun ω => (F ω).toReal) M G (fun _ => 0) (g x + δ)
    hF.ennreal_toReal.aestronglyMeasurable (Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))
    hMI hM0 hG (Filter.Eventually.of_forall (fun _ => le_rfl)) hBudget
  change (∫⁻ ω, F ω ∂P) ≤ _
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (F ω).toReal ∂P := by
      apply lintegral_congr
      intro ω
      exact (ENNReal.ofReal_toReal (ne_of_lt
        (avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
          D hD.1.1 ω (ruinTime X x D ω) (θ ω) q hq.le))).symm
    _ ≤ _ := hb
