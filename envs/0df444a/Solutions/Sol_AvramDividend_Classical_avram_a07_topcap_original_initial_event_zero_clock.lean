-- Prove2me | solution 1 for AvramDividend.Classical.avram_a07_topcap_original_initial_event_zero_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:51:04.735781+00:00
-- url     : https://prove2.me/submissions/905d04a4-bfb2-462f-994d-fadeb54fb655

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_avram_p4_f8_original_exact_clock_zero_reward_le_initial
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration
ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬
X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C :
ℝ≥0∞) (hC : 0 < C) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y <
0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
(hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧
X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤
deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD :
IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D
ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) <
ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w
(riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (σ : Ω →
ℝ≥0) (hσstop : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0))) (hσbound : ∀
ω, σ ω ≤ (n : ℝ≥0)) (hσclip : ∀ ω, σ ω ≤ (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
(F : Ω → ℝ) (hFsource : ∀ ω, F ω = Real.exp (-(q * (σ ω : ℝ))) * w (if σ ω = 0 ∨ (σ ω :
ℝ≥0∞) < ruinTime X x D ω then x + X.X (σ ω) ω - rightLimit D (σ ω) ω else riskProcess X
x D (σ ω) ω) + (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ), ENNReal.ofReal
(Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) (hFI : Integrable F P)
(hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤) (hCtop : C = ⊤) (R : ℝ≥0 → Ω → ℝ) (hRsource :
∀ᵐ ω ∂P, ∀ t : ℝ≥0, Tendsto (fun k : ℕ =>
avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω) atTop (nhds (R t ω)))
(hRadapt : ∀ t : ℝ≥0, AEStronglyMeasurable[𝓕.rightCont t] (R t) P) (hRint : ∀ t : ℝ≥0,
Integrable (R t) P) (hRmart : ∀ s t : ℝ≥0, s ≤ t → ∀ᵐ ω ∂P, condExp (𝓕.rightCont s) P
(R t) ω = R s ω) (hRbracket : ∀ t : ℝ≥0, Integrable (fun ω => (R t ω) ^ 2) P ∧ (∫ ω, (R
t ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2) (hJstopped : ∃ Jsmall : ℝ≥0 → Ω → ℝ, (∀ᵐ ω ∂P, ∀ t :
ℝ≥0, Tendsto (fun k : ℕ => avram_p4_h_gaussian_intrinsic_small_band_compensated X k t
ω) atTop (nhds (Jsmall t ω))) ∧ (∀ t : ℝ≥0, Integrable (Jsmall t) P) ∧ (∀ s t : ℝ≥0, s
≤ t → ∀ᵐ ω ∂P, condExp (𝓕.rightCont s) P (Jsmall t) ω = Jsmall s ω) ∧ Integrable (fun
ω => Jsmall (σ ω) ω) P ∧ (∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P (fun ω => Jsmall (σ ω) ω)
ω = 0)) : ∀ S : Set Ω, MeasurableSet[𝓕.rightCont 0] S → ∫ ω in S ∩ {ω : Ω | (σ ω =
0)}, F ω ∂P ≤ (P (S ∩ {ω : Ω | (σ ω = 0)})).toReal * w x := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro S hS
  let A : Set Ω := S ∩ {ω : Ω | σ ω = 0}
  have hA : MeasurableSet A := by
    have hzero : MeasurableSet[𝓕.rightCont 0] {ω : Ω | σ ω = 0} := by
      have heq : {ω : Ω | σ ω = 0} =
          {ω : Ω | (σ ω : WithTop ℝ≥0) = 0} := by
        ext ω
        change σ ω = 0 ↔ (σ ω : WithTop ℝ≥0) = 0
        constructor
        · intro h; rw [h]; simp
        · intro h; exact_mod_cast h
      rw [heq]
      exact hσstop.measurableSet_eq (0 : ℝ≥0)
    exact (𝓕.rightCont.le 0) _ (hS.inter hzero)
  have hpoint : ∀ ω ∈ A, F ω ≤ w x := by
    intro ω hω
    have hz : σ ω = 0 := hω.2
    have h := avram_p4_f8_original_exact_clock_zero_reward_le_initial
      X x q w C D hD hjump
      (fun _ : ℕ => σ) (fun _ : ℕ => F)
      (by intro k ξ; exact hFsource ξ) (0 : ℕ) ω hz
    exact h
  have hint : IntegrableOn F A P := hFI.integrableOn
  have hconst : IntegrableOn (fun _ : Ω => w x) A P :=
    (integrable_const (w x) : Integrable (fun _ : Ω => w x) P).integrableOn
  have hle : (∫ ω in A, F ω ∂P) ≤ (∫ ω in A, (w x : ℝ) ∂P) :=
    setIntegral_mono_on hint hconst hA hpoint
  simpa only [A, setIntegral_const, measureReal_def, smul_eq_mul] using hle
