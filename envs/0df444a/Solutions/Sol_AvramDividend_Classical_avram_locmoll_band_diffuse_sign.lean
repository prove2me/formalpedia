-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_band_diffuse_sign
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:59:44.151444+00:00
-- url     : https://prove2.me/submissions/d539e234-487c-4762-aef6-6238bd2183d3

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
    let J : Ω → ℝ≥0 → ℝ := fun ω s =>
      if s ≤ θ ω ∧ (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) then
        Real.exp (-(q * (s : ℝ))) *
          ((rightLimit D s ω - D s ω) +
            g (x + X.X s ω - rightLimit D s ω) - g (riskProcess X x D s ω))
      else 0
    let Diff : Ω → ℝ := fun ω =>
      ∫ t in (paymentTimes (ruinTime X x D ω) ∩ Ioc (0 : ℝ) (θ ω : ℝ)),
        Real.exp (-(q * t)) *
          (1 - deriv g (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t.toNNReal))
        ∂((dividendMeasure D ω).restrict
          {t : ℝ | rightLimit D t.toNNReal ω = D t.toNNReal ω})
    ∀ ω, Diff ω ≤ 0 := by 
  dsimp only
  intro ω
  apply integral_nonpos_of_ae
  have hm : MeasurableSet (paymentTimes (ruinTime X x D ω) ∩ Ioc (0 : ℝ) (θ ω : ℝ)) := by
    unfold paymentTimes
    measurability
  filter_upwards [ae_restrict_mem hm] with t ht
  have hle : t.toNNReal ≤ θ ω := by
    simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal ht.2.2
  have hp := avram_locmoll_band_left_limit_cap X x C D hD δ R θ hprefix ω
    t.toNNReal (Real.toNNReal_pos.mpr ht.2.1) hle
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr (hGrad _ hp.1.1))
