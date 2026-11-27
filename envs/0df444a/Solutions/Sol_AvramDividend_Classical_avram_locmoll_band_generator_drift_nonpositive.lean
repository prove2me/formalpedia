-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_band_generator_drift_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:57:29.958001+00:00
-- url     : https://prove2.me/submissions/8e892e3b-f4b4-44fc-ba50-697722cffa04

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_left_limit_cap
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
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (C : ℝ≥0∞) (hC : 0 < C)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T)
    (δ R : ℝ) (hδ : 0 < δ) (hδx : δ < x) (hxR : x < R)
    (θ : Ω → ℝ≥0)
    (hθle : ∀ ω, θ ω ≤ T.toNNReal)
    (hprefix : ∀ ω t, t < θ ω →
      x + X.X t ω - rightLimit D t ω ∈ Icc δ R)
    (hstop : IsStoppingTime 𝓕.rightCont (fun ω => (θ ω : WithTop ℝ≥0)))
    (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (hNonneg : ∀ y : ℝ, 0 ≤ g y)
    (hZero : ∀ y : ℝ, y ≤ 0 → g y = 0)
    (hGrad : ∀ y : ℝ, δ ≤ y → 1 ≤ deriv g y)
    (hGen : ∀ y : ℝ, δ ≤ y → ENNReal.ofReal y ≤ C →
      X.GeneratorIntegrable g y ∧ X.generator g y - q * g y ≤ 0)
    (hSec : ∀ a b : ℝ, δ ≤ b → b ≤ a →
      a - b ≤ g a - g b)
    (hLoss : ∀ a b : ℝ, 0 ≤ b → b ≤ a →
      a - b ≤ g a - g b + δ) :
    ∀ ω, (fun ω : Ω => ∫ t in Ioc (0 : ℝ) (θ ω : ℝ),
      Real.exp (-(q * t)) *
        (X.generator g (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t.toNNReal) -
          q * g (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t.toNNReal))) ω ≤ 0 := by 
  intro ω
  apply integral_nonpos_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : 0 < t := ht.1
  have ht' : 0 < t.toNNReal := Real.toNNReal_pos.mpr ht0
  have hle : t.toNNReal ≤ θ ω := by
    simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal ht.2
  obtain ⟨hb, hc⟩ := avram_locmoll_band_left_limit_cap X x C D hD δ R θ hprefix ω t.toNNReal ht' hle
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (hGen _ hb.1 hc).2
