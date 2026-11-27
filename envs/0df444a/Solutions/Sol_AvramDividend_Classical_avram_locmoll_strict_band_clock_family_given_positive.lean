-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_strict_band_clock_family_given_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:03:04.94471+00:00
-- url     : https://prove2.me/submissions/0deb9c23-067e-4d1c-b6da-082f5b845aab

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_sequence
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_grid_band_clock_family
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_random_closed_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_cash_coverage
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_nested_cash_convergence
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
    (η : ℝ) (hη : 0 < η)
    (hpos : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T.toNNReal →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 < x + X.X t ω - rightLimit D t ω) :
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
  obtain ⟨δ, R, hb, hηb, ha, hm, hd, hR⟩ :=
    avram_locmoll_band_sequence x η hx hη
  obtain ⟨θ, hle, hp, hs, hmono, hcover⟩ :=
    avram_locmoll_grid_band_clock_family X x D hD.1.1 T.toNNReal δ R ha hm
  refine ⟨δ, R, θ, hb, hηb, hd, hR, hle, hp, hs, ?_, ?_⟩
  · intro k
    exact avram_locmoll_random_closed_cash_measurable X x D hD.1.1 q (θ k) (hs k)
  · exact avram_locmoll_nested_cash_convergence X x D hD.1.1 q T hT θ hle hmono
      (avram_locmoll_band_cash_coverage X x D hD.1.1 T hT δ R hd hR θ hcover hpos)
