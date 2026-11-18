-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f7_infinitecap_natural_terminal_L1_expected_upper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T00:39:37.9271+00:00
-- url     : https://prove2.me/submissions/df42d508-ca75-4f8c-88c3-ff2585d7b69f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva42_ubv_topcap_natural_stopped_reward_ENNReal_expected_source
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_infinite_cap_discounted_terminal_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_gradient_value_nonnegative_on_compact_interval
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_allcap_ennreal_expected_budget_implies_terminal_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

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
    (hCashI : Integrable Cash P) (hTop : C = ⊤) :
    Integrable Term P ∧
      (∫ ω, Term ω + Cash ω ∂P) ≤ w x := by
  have hWx : 0 ≤ w x := by
    have hInside : ENNReal.ofReal x < C := by
      simp only [hTop]
      exact ENNReal.ofReal_lt_top
    have hr :=
      avram_wave7_02_original_positive_cap_C1_gradient_value_nonnegative_on_compact_interval
        C hC w hw_cont hw0 (hw_smooth.of_le (by norm_num)) hw_grad
        x hx.le hInside
    exact hr x (Set.mem_Icc.mpr ⟨hx.le, le_rfl⟩)
  have hTermPos : ∀ᵐ ω ∂P, 0 ≤ Term ω := by
    filter_upwards [] with ω
    exact avram_p4_f_assembly_original_infinite_cap_discounted_terminal_nonnegative
      X q w C hTop hw0 hw_cont hw_neg hw_smooth hw_grad
      x D τ W Term hW hTerm ω
  have hCashPos : ∀ᵐ ω ∂P, 0 ≤ Cash ω := by
    filter_upwards [] with ω
    rw [hCash ω]
    exact ENNReal.toReal_nonneg
  have hSource :=
    avram_bva42_ubv_topcap_natural_stopped_reward_ENNReal_expected_source
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm
      hTermMeas hCashI hTop
  exact avram_p4_e_localise_original_allcap_ennreal_expected_budget_implies_terminal_L1
    w x hWx Term Cash hTermMeas hCashI hTermPos hCashPos hSource
