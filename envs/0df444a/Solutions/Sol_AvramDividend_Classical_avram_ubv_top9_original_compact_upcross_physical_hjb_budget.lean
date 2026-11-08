-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top9_original_compact_upcross_physical_hjb_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:00:31.802714+00:00
-- url     : https://prove2.me/submissions/86206ee0-4ea6-499f-9e76-872a3d11c49a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_physical_gaussian_small_large_signed_budget_core
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_source_signed_witness_to_expected_upper
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_compact_original_reward_L1_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Reduce the compact physical Ito budget to the original signed triplet core. -/
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
    (hFI : ∀ k, Integrable (F k) P) (hinfinite : C = ⊤) :
    ∀ k, ∀ (κ : ℕ → Ω → ℝ≥0)
      (hκstop : ∀ j, IsStoppingTime 𝓕.rightCont
        (fun ω => (κ j ω : WithTop ℝ≥0)))
      (hκle : ∀ j ω, κ j ω ≤ σ k ω)
      (hκbound : ∀ j ω, X.X (κ j ω) ω ≤ (j : ℝ) + 1)
      (H : ℕ → Ω → ℝ),
      (∀ j ω, H j ω =
        Real.exp (-(q * (κ j ω : ℝ))) *
          w (if κ j ω = 0 ∨ (κ j ω : ℝ≥0∞) < ruinTime X x D ω then
              x + X.X (κ j ω) ω - rightLimit D (κ j ω) ω
            else riskProcess X x D (κ j ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ j ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) →
      ∀ j, (∫ ω, H j ω ∂P) ≤ w x := by
  classical
  intro k κ hκstop hκle hκbound H hHsource j
  have hκleτ : ∀ i ω, κ i ω ≤ τ ω := fun i ω =>
    (hκle i ω).trans (hσle k ω)
  have hCashτI : Integrable (fun ω =>
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) P := by
    have he : (fun ω =>
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) =
        Cash := funext (fun ω => (hCash ω).symm)
    rw [he]
    exact hCashI
  have hκmeas : ∀ i, Measurable (fun ω : Ω => (κ i ω : ℝ)) := fun i =>
    avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable
      (κ i) (hκstop i)
  have hHI : ∀ i, Integrable (H i) P :=
    fun i => (avram_ubv_top9_compact_original_reward_L1_nonnegative
      X hBV q (le_of_lt hq) w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hxc D hD τ hCashτI κ hκstop hκleτ hκbound H hHsource i).1
  obtain ⟨Mc, Ms, Ml, G, R, hMcI, hMsI, hMlI,
    hMc0, hMs0, hMl0, hG, hR, hIto⟩ :=
    avram_ubv_loc6_physical_gaussian_small_large_signed_budget_core
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas hτstop
      W Cash Term hW hCash hTerm hTermMeas hCashI
      κ H hκstop hκleτ hHsource hHI j
  exact avram_ubv_top9_original_source_signed_witness_to_expected_upper
    X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
    x hx hxc D hD q (κ j) (hκstop j) (H j) (hHsource j) (hHI j)
    Mc Ms Ml G R hMcI hMsI hMlI hMc0 hMs0 hMl0 hG hR hIto
