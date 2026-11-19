-- Prove2me | solution 6 for AvramDividend.Classical.avram_f7_original_any_compact_clock_ito_signed_source_witnesses
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:11:52.314897+00:00
-- url     : https://prove2.me/submissions/28717649-37cf-43a6-815b-dd793cc800f2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_positive_clock_ito_meyer_signed_witness
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_zero_clock_exact_physical_F_le
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal



theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
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
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hStop : (∀ k, IsStoppingTime 𝓕.rightCont
        (fun ω => (σ k ω : WithTop ℝ≥0))))
    (hBound : (∀ k ω, σ k ω ≤ τ ω))
    (hExact : (∀ k ω, F k ω =
        Real.exp (-(q * (σ k ω : ℝ))) *
          w (if σ k ω = 0 ∨
                (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
              x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
            else riskProcess X x D (σ k ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal))
    (hMeas : (∀ k, Measurable (F k)))
    (hInt : (∀ k, Integrable (F k) P))
    (hNonneg : (∀ k, 0 ≤ᵐ[P] F k)) :
    ∀ k : ℕ, ∃ M G H : Ω → ℝ,
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, F k ω ≤ w x + M ω + G ω + H ω) := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro k
  obtain ⟨Mc, Ms, Ml, G, R, hMaskMeas, hMaskPos,
    hMcI, hMsI, hMlI, hMc0, hMs0, hMl0, hG, hR, hDom⟩ :=
    avram_ubv_loc6_original_positive_clock_ito_meyer_signed_witness
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop W Cash Term
      hW hCash hTerm hTermMeas hCashI
      σ F hStop hBound hExact hInt k
  let M : Ω → ℝ := Mc + (Ms + Ml)
  have hMI : Integrable M P := hMcI.add (hMsI.add hMlI)
  have hMsMl0 : (∫ ω, (Ms + Ml) ω ∂P) = 0 :=
    (integral_add hMsI hMlI).trans (by rw [hMs0, hMl0]; norm_num)
  have hMzero : (∫ ω, M ω ∂P) = 0 := by
    calc
      (∫ ω, M ω ∂P) =
          (∫ ω, Mc ω ∂P) + (∫ ω, (Ms + Ml) ω ∂P) :=
        integral_add hMcI (hMsI.add hMlI)
      _ = 0 := by rw [hMc0, hMsMl0]; norm_num
  have hMasked : ∀ᵐ ω ∂P,
      (if σ k ω = 0 then w x else F k ω) ≤ w x + M ω := by
    filter_upwards [hDom, hG, hR] with ω hω hGω hRω
    dsimp [M]
    linarith
  have hFle : ∀ᵐ ω ∂P, F k ω ≤ w x + M ω := by
    filter_upwards [hMasked] with ω hω
    by_cases hz : σ k ω = 0
    · have hInit : F k ω ≤ w x :=
        avram_ubv_loc6_original_zero_clock_exact_physical_F_le
          X x q w C D hD hjump σ F hExact k ω hz
      simp only [hz, if_pos] at hω
      linarith
    · simpa only [if_neg hz] using hω
  have hZeroI : Integrable (fun _ : Ω => (0 : ℝ)) P :=
    integrable_const 0
  refine ⟨M, (fun _ => 0), (fun _ => 0),
    hMI, hZeroI, hZeroI, hMzero, ?_, ?_⟩
  · filter_upwards [] with ω
    simp
  · simpa only [add_zero] using hFle
