-- Prove2me | solution 1 for AvramDividend.Classical.avram_jb26_original_positive_clock_eventwise_cash
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T11:01:23.655015+00:00
-- url     : https://prove2.me/submissions/2fdae151-5067-4b13-ae55-aed98f98d0d5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_jb27_original_positive_clock_ito_certificate
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin24_initial_event_condcentered_mask_transfer
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin22_positive_initial_from_closed_cap_gradient
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_positive_clock_initial_measurable
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin36_original_finitecap_any_stopped_full_reward_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! The genuine physical Itô-source child supplies the signed noise certificate. -/

/-- The original stopped cash event budget follows from a same-filtration Itô certificate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
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
    (n : ℕ) (hn : 0 < n) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (hρclip : ∀ ω, ρ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hCfinite : C ≠ ⊤)
    (κ : ℕ → Ω → ℝ≥0)
    (hκexact : ∀ k ω, κ k ω =
      (min (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal)
    (hκstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (κ k ω : WithTop ℝ≥0)))
    (H : ℕ → Ω → ℝ)
    (hHsource : ∀ k ω, H k ω =
      Real.exp (-(q * (κ k ω : ℝ))) *
        w (if κ k ω = 0 ∨
              (κ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (κ k ω) ω - rightLimit D (κ k ω) ω
          else riskProcess X x D (κ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) :
    ∀ k (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
      (∫ ω in A ∩ {η : Ω | κ k η ≠ 0}, H k ω ∂P) ≤
        w x * (P (A ∩ {η : Ω | κ k η ≠ 0})).toReal := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hwx : 0 ≤ w x :=
    avram_mix_fin22_positive_initial_from_closed_cap_gradient
      C hC w hw0 hw_cont hw_smooth hw_grad x hx hxc
  intro k A hA
  obtain ⟨M, B, hMI, hM0, hBsign, hLedger⟩ :=
    avram_jb27_original_positive_clock_ito_certificate
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg
      hjump n hn ρ hρstop hρbound hρclip hFiniteActivity
      hCfinite κ hκexact hκstop H hHsource k A hA
  let E : Set Ω := A ∩ {η : Ω | κ k η ≠ 0}
  have hE : MeasurableSet[𝓕.rightCont 0] E :=
    hA.inter (avram_ubv_finite12_positive_clock_initial_measurable
      (κ k) (hκstop k))
  have hκbound : ∀ ω, κ k ω ≤ (n : ℝ≥0) := by
    intro ω
    have hmin := ENNReal.toNNReal_mono
      (show (ρ ω : ℝ≥0∞) ≠ ⊤ by simp)
      (min_le_left (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((k : ℝ) + 1) ω))
    have hmin' :
        (min (ρ ω : ℝ≥0∞)
          (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal ≤ ρ ω := by
      simpa using hmin
    rw [hκexact k ω]
    exact hmin'.trans (hρbound ω)
  have hHI : Integrable (H k) P :=
    avram_mix_fin36_original_finitecap_any_stopped_full_reward_L1
      X x q (le_of_lt hq) w hw_cont hw_neg C hCfinite hxc
      D hD n (κ k) (hκstop k) hκbound (H k) (hHsource k)
  have hLedger' : ∀ᵐ ω ∂(P.restrict E),
      H k ω ≤ w x + M ω := by
    filter_upwards [hBsign, hLedger] with ω hb hω
    linarith
  change (∫ ω in E, H k ω ∂P) ≤ w x * (P E).toReal
  exact avram_mix_fin24_initial_event_condcentered_mask_transfer
    (𝓕.rightCont 0) ((𝓕.rightCont).le 0)
    E E hE (Subset.rfl) (w x) hwx (H k) M hHI hMI hM0 hLedger'
