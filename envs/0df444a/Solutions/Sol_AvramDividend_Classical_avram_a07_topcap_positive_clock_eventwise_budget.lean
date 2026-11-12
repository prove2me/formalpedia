-- Prove2me | solution 1 for AvramDividend.Classical.avram_a07_topcap_positive_clock_eventwise_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:41:46.7672+00:00
-- url     : https://prove2.me/submissions/963040d3-2020-4da7-9871-108f3d7871e3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_avram_a07_topcap_original_two_noise_martingale_majorant

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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
    (n : ℕ) (hn : 0 < n) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (hσclip : ∀ ω, σ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X x D ω then
          x + X.X (σ ω) ω - rightLimit D (σ ω) ω
        else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hFI : Integrable F P)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hCtop : C = ⊤) :
    ∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
      (∫ ω in A ∩ {η : Ω | σ η ≠ 0}, F ω ∂P) ≤
        w x * (P (A ∩ {η : Ω | σ η ≠ 0})).toReal := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨MG, MJ, hMGI, hMJI, hMG0, hMJ0, hUpper⟩ :=
    avram_a07_topcap_original_two_noise_martingale_majorant
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn σ hσstop hσbound hσclip F hFsource hFI hFiniteActivity hCtop
  have hσzero := hσstop 0
  have hσpositive : MeasurableSet[𝓕.rightCont 0] {ω : Ω | σ ω ≠ 0} := by
    have hset : {ω : Ω | σ ω ≠ 0} =
        {ω : Ω | (σ ω : WithTop ℝ≥0) ≤ (0 : ℝ≥0)}ᶜ := by
      ext ω
      change (σ ω ≠ 0) ↔ ¬ ((σ ω : WithTop ℝ≥0) ≤ 0)
      constructor
      · intro hne hle
        have hle' : σ ω ≤ 0 := by
          exact_mod_cast hle
        exact hne (le_antisymm hle' (zero_le : (0 : ℝ≥0) ≤ σ ω))
      · intro hne hz
        apply hne
        simp [hz]
    rw [hset]
    exact hσzero.compl
  have hBudget : ∀ B : Set Ω, MeasurableSet[𝓕.rightCont 0] B →
      (∫ ω in B, F ω ∂P) ≤ w x * (P B).toReal := by
    intro B hB
    have hZeroIntegral (M : Ω → ℝ) (hMI : Integrable M P)
        (hCond : ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P M ω = 0) :
        (∫ ω in B, M ω ∂P) = 0 := by
      calc
        (∫ ω in B, M ω ∂P) =
            ∫ ω in B, condExp (𝓕.rightCont 0) P M ω ∂P :=
          (setIntegral_condExp (𝓕.rightCont.le 0) hMI hB).symm
        _ = 0 := integral_eq_zero_of_ae (ae_restrict_of_ae hCond)
    have hMGzero := hZeroIntegral MG hMGI hMG0
    have hMJzero := hZeroIntegral MJ hMJI hMJ0
    have hconst : Integrable (fun _ : Ω => (w x)) P := integrable_const (w x)
    have hsum : Integrable (fun ω => (w x) + MG ω) P := hconst.add hMGI
    calc
      (∫ ω in B, F ω ∂P) ≤
          ∫ ω in B, (w x) + MG ω + MJ ω ∂P :=
        setIntegral_mono_ae hFI.integrableOn (hsum.add hMJI).integrableOn
          hUpper
      _ = (∫ ω in B, (w x) + MG ω ∂P) +
          (∫ ω in B, MJ ω ∂P) := by
        rw [integral_add hsum.integrableOn hMJI.integrableOn]
      _ = (∫ ω in B, (w x) ∂P) +
          (∫ ω in B, MG ω ∂P) +
          (∫ ω in B, MJ ω ∂P) := by
        rw [integral_add hconst.integrableOn hMGI.integrableOn]
      _ = (∫ ω in B, (w x) ∂P) := by
        simp [hMGzero, hMJzero]
      _ = (w x) * (P B).toReal := by
        rw [integral_const]
        simp only [Measure.real, Measure.restrict_apply_univ]
        ring
  intro A hA
  exact hBudget (A ∩ {ω : Ω | σ ω ≠ 0}) (hA.inter hσpositive)
