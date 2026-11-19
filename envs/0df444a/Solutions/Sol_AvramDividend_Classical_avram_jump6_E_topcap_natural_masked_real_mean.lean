-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_E_topcap_natural_masked_real_mean
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:26:26.958442+00:00
-- url     : https://prove2.me/submissions/cb049812-6904-4043-994d-7e8473ca91ca
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

import Theorems.Thm_AvramDividend_Classical_avram_jump6_E_topcap_original_positive_clock_expected_upper
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn10_clock_partition_mean_upper
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

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
    (hTermI : Integrable Term P)
    (hTop : C = ⊤) :
    (∫ ω, if τ ω = 0 then w x else Term ω + Cash ω ∂P) ≤ w x := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let F : Ω → ℝ := fun ω => Term ω + Cash ω
  have hFI : Integrable F P := hTermI.add hCashI
  have hSrc : ∀ (k : ℕ) (ω : Ω), F ω =
      Real.exp (-(q * (τ ω : ℝ))) *
        w (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
          x + X.X (τ ω) ω - rightLimit D (τ ω) ω
        else riskProcess X x D (τ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by
    intro k ω
    dsimp [F]
    rw [hTerm ω, hCash ω, hW ω]
  have hZ : MeasurableSet {ω : Ω | τ ω = 0} :=
    avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable 𝓕 τ hτstop
  have hPositive : (∫ ω in {ω : Ω | τ ω ≠ 0}, F ω ∂P) ≤
      w x * (P {ω : Ω | τ ω ≠ 0}).toReal :=
    (avram_jump6_E_topcap_original_positive_clock_expected_upper
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
    hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
    n hn τ hτeq hτmeas hτstop W Cash Term
    hW hCash hTerm hTermMeas hCashI (fun _ => τ) (fun _ => F)
      (by intro k; exact hτstop)
      (by intro k ω; exact le_refl _)
      (by intro k ω; exact hSrc k ω)
      (by intro k; exact hFI) hTop) 0
  let Z : Set Ω := {ω : Ω | τ ω = 0}
  let Mask : Ω → ℝ := fun ω => if τ ω = 0 then w x else F ω
  have hMaskEq : Mask = fun ω =>
      Z.indicator (fun _ => w x) ω + Zᶜ.indicator F ω := by
    funext ω
    by_cases hz : τ ω = 0 <;> simp [Mask, Z, Set.indicator, hz]
  have hMaskI : Integrable Mask P := by
    rw [hMaskEq]
    exact ((integrable_const (w x)).indicator hZ).add
      (hFI.indicator hZ.compl)
  have hPosMask : (∫ ω in {ω : Ω | τ ω ≠ 0}, Mask ω ∂P) ≤
      w x * (P {ω : Ω | τ ω ≠ 0}).toReal := by
    have hEq : (∫ ω in {ω : Ω | τ ω ≠ 0}, Mask ω ∂P) =
        (∫ ω in {ω : Ω | τ ω ≠ 0}, F ω ∂P) := by
      exact setIntegral_congr_fun hZ.compl
        (by intro ω hω; simp only [Set.mem_setOf_eq] at hω; simp [Mask, hω])
    exact hEq.trans_le hPositive
  have hMean : (∫ ω, Mask ω ∂P) ≤ w x :=
    avram_ubv_finite9_turn10_clock_partition_mean_upper
      (w x) τ Mask hZ hMaskI
      (by intro ω hz; simp [Mask, hz]) hPosMask
  simpa [Mask, F] using hMean
