-- Prove2me | solution 1 for AvramDividend.Classical.avram_a07_topcap_original_positive_clock_condexp_supermartingale_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:50:52.676419+00:00
-- url     : https://prove2.me/submissions/ea8f88a2-ddd1-45a4-9499-b070d79384cd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a07_original_global_two_noise_signed_stopped_reward
import Theorems.Thm_AvramDividend_Classical_avram_a07_condexp_upper_of_two_centered_noises
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
ω = 0)) :
    ∀ S : Set Ω, MeasurableSet[𝓕.rightCont 0] S →
    ∀ᵐ ω ∂(P.restrict (S ∩ {η : Ω | σ η ≠ 0})),
      P[F | 𝓕.rightCont 0] ω ≤ w x := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨MG, MJ, B, hMGI, hMJI, hMG0, hMJ0, hLedger⟩ :=
    avram_a07_original_global_two_noise_signed_stopped_reward
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump n hn σ hσstop hσbound hσclip
      F hFsource hFI hFiniteActivity hCtop R hRsource hRadapt hRint hRmart
      hRbracket hJstopped
  have hUpper : ∀ᵐ ω ∂P, F ω ≤ w x + MG ω + MJ ω := by
    filter_upwards [hLedger] with ω hω
    linarith [hω.1, hω.2]
  have hCond : P[F | 𝓕.rightCont 0] ≤ᵐ[P] (fun _ : Ω => w x) :=
    avram_a07_condexp_upper_of_two_centered_noises
      (𝓕 := 𝓕) (w x) F MG MJ hFI hMGI hMJI hMG0 hMJ0 hUpper
  intro S hS
  exact ae_restrict_of_ae hCond
