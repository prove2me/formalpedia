-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_strict_band_clock_family
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:52:52.44114+00:00
-- url     : https://prove2.me/submissions/79d4378f-21b1-46f0-844e-21a2e4745d81
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_strict_band_clock_family_given_positive
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_bounded_preruin_strict_positive
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
    (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (C : ℝ≥0∞)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T)
    (η : ℝ) (hη : 0 < η) :
    ∃ (δ R : ℕ → ℝ) (θ : ℕ → Ω → ℝ≥0),
      (∀ k, 0 < δ k ∧ δ k < x ∧ x < R k) ∧
      (∀ k, δ k ≤ η) ∧
      Tendsto δ atTop (𝓝 0) ∧ Tendsto R atTop atTop ∧
      (∀ k ω, θ k ω ≤ T.toNNReal) ∧
      (∀ k ω t, t < θ k ω →
        x + X.X t ω - rightLimit D t ω ∈ Icc (δ k) (R k)) ∧
      (∀ k, IsStoppingTime 𝓕.rightCont
        (fun ω => (θ k ω : WithTop ℝ≥0))) ∧
      let F : ℕ → Ω → ℝ≥0∞ := fun k ω =>
        ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (θ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
      let V : Ω → ℝ≥0∞ := fun ω =>
        ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
      (∀ k, AEMeasurable (F k) P) ∧
      (∀ᵐ ω ∂P, Tendsto (fun k => F k ω) atTop (𝓝 (V ω))) := by 
  exact avram_locmoll_strict_band_clock_family_given_positive
    X hX hBV q C x hx hxc D hD T hT η hη
    (avram_locmoll_bounded_preruin_strict_positive X hBV x C D hD T.toNNReal)
