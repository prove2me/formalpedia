-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss_top15_original_zero_nu_ruin_clipped_strict_expected_upper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T13:40:34.440787+00:00
-- url     : https://prove2.me/submissions/52658435-f60b-4b87-a7af-7ebaa6fd5da8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_avram_gtop15_original_compact_prefix_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_gtop15_original_compact_stopped_C2_reward_budget
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_ae_natural_clock_fatou_L1_budget
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss_top14_original_strict_masked_reward_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss_top15_original_strict_stopped_reward_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_topcap_w_nonnegative_everywhere

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Physical compact-prefix source plus original clipped exhaustion imply the strict top-cap budget via nonnegative Fatou. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
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
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k, (∫ ω,
      if σ k ω = 0 then w x else
        Real.exp (-(q * (σ k ω : ℝ))) *
          w (riskProcess X x D (σ k ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal ∂P) ≤ w x := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k
  let H : (Ω → ℝ≥0) → Ω → ℝ := fun ζ ω =>
    if ζ ω = 0 then w x else
      Real.exp (-(q * (ζ ω : ℝ))) *
        w (riskProcess X x D (ζ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ζ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal
  change (∫ ω, H (σ k) ω ∂P) ≤ w x
  obtain ⟨ρ, hρstop, hρle, hρmeas, hSmeas, hprefix, hlim⟩ :=
    avram_gtop15_original_compact_prefix_exhaustion
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad x hx hxc
      D hD hw_nonneg hjump n hn τ hτeq hτstop
      (σ k) (hσstop k) (hσle k)
  have hclock : ∀ ω, τ ω ≤ (n : ℝ≥0) := by
    intro ω
    calc
      τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal := hτeq ω
      _ ≤ (n : ℝ≥0) :=
        (avram_wave7_08_source_truncated_clock_nnreal_bounds X x D n).2.1 ω
  have hρbound : ∀ j ω, ρ j ω ≤ (n : ℝ≥0) := by
    intro j ω
    exact (hρle j ω).trans ((hσle k ω).trans (hclock ω))
  have hFint : ∀ j, Integrable (H (ρ j)) P := by
    intro j
    have hi := avram_ubv_gauss_top14_original_strict_masked_reward_L1
      X hX hBV hNuZero q hq w C hC hTopCap
      hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
      x D hD (fun _ => ρ j) (fun _ => hρstop j)
      n (fun _ ω => hρbound j ω) 0
    simpa only [H] using hi
  have hFnonneg : ∀ j, 0 ≤ᵐ[P] H (ρ j) := by
    intro j
    have hp := avram_ubv_gauss_top15_original_strict_stopped_reward_nonnegative
      X hNuZero w C hTopCap hw0 hw_cont hw_neg hw_smooth
      hw_grad q x D (fun _ => ρ j)
    exact Filter.Eventually.of_forall (fun ω => by
      simpa only [H, Pi.zero_apply] using hp 0 ω)
  have hSnonneg : 0 ≤ᵐ[P] H (σ k) := by
    have hp := avram_ubv_gauss_top15_original_strict_stopped_reward_nonnegative
      X hNuZero w C hTopCap hw0 hw_cont hw_neg hw_smooth
      hw_grad q x D (fun _ => σ k)
    exact Filter.Eventually.of_forall (fun ω => by
      simpa only [H, Pi.zero_apply] using hp 0 ω)
  have hBudget : ∀ j, (∫ ω, H (ρ j) ω ∂P) ≤ w x := by
    intro j
    exact avram_gtop15_original_compact_stopped_C2_reward_budget
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad x hx hxc
      D hD hw_nonneg hjump n hn τ hτeq hτstop
      (ρ j) (hρstop j) (fun ω => (hρle j ω).trans (hσle k ω))
      j (hprefix j)
  have hwx : 0 ≤ w x :=
    avram_ubv_top9_original_topcap_w_nonnegative_everywhere
      w C hTopCap hw0 hw_cont hw_neg hw_smooth hw_grad x
  have hFatou := avram_p4_f4_ae_natural_clock_fatou_L1_budget
    P (H (σ k)) (fun j => H (ρ j))
    hSmeas hSnonneg hρmeas hFint hFnonneg hlim
    (w x) hwx hBudget
  exact hFatou.2
