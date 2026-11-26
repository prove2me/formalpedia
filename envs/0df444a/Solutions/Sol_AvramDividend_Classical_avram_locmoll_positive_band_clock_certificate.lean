-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_positive_band_clock_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:52:52.78706+00:00
-- url     : https://prove2.me/submissions/12b9d117-07d5-44e7-a836-14812e313742
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_strict_band_clock_family
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_smooth_test_certificate
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_smooth_band_stopped_cash_bound
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_lower_strip_dividend_loss
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_restricted_secant_convolution
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) :
    ∀ η : ℝ, 0 < η →
      ∃ (δ R : ℕ → ℝ) (θ : ℕ → Ω → ℝ≥0),
        (∀ k, 0 < δ k ∧ δ k < x ∧ x < R k) ∧
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
        (∀ᵐ ω ∂P, Tendsto (fun k => F k ω) atTop (𝓝 (V ω))) ∧
        (∀ k, (∫⁻ ω, F k ω ∂P) ≤ ENNReal.ofReal (w x + η)) := by 
  intro η hη
  obtain ⟨δ, R, θ, hband, hslack, hd, hR, hθle, hprefix, hstop, hm, hlim⟩ :=
    avram_locmoll_strict_band_clock_family
      X hX hBV q C x hx hxc D hD T hT η hη
  refine ⟨δ, R, θ, hband, hd, hR, hθle, hprefix, hstop, hm, hlim, ?_⟩
  intro k
  obtain ⟨hδ, hδx, hxR⟩ := hband k
  obtain ⟨V, ρ, g, hρI, hnorm, hρpos, hsupport, hVsec, hI,
      hgEq, hg, hmono, hnonneg, hzero, hgrad, hgen, hgx⟩ :=
    avram_locmoll_smooth_test_certificate
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_hjb x hx hxc (δ k) hδ hδx
  have hs : ∀ a b : ℝ, δ k ≤ b → b ≤ a →
      a - b ≤ g a - g b := by
    intro a b hb hba
    have h := avram_locmoll_restricted_secant_convolution
      volume ρ V (δ k / 3) b a a (by linarith)
      (by linarith) hba le_rfl hρI hnorm hρpos hsupport
      (fun u v hu huv _ => hVsec u v hu huv) (hI b) (hI a)
    rw [← hgEq a, ← hgEq b] at h
    exact h
  have hloss : ∀ a b : ℝ, 0 ≤ b → b ≤ a →
      a - b ≤ g a - g b + δ k := by
    intro a b hb hba
    exact avram_locmoll_lower_strip_dividend_loss
      g (δ k) hδ.le hmono
      (fun u v hu huv => hs v u hu huv) a b hb hba
  exact (avram_locmoll_smooth_band_stopped_cash_bound
    X hX hBV q hq C hC x hx hxc D hD T hT (δ k) (R k)
    hδ hδx hxR (θ k) (hθle k) (hprefix k) (hstop k) g hg hnonneg hzero
    hgrad hgen hs hloss).trans
    (ENNReal.ofReal_le_ofReal (add_le_add hgx (hslack k)))
