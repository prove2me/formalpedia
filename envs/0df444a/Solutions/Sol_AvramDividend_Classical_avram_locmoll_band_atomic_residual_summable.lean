-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_band_atomic_residual_summable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:25:21.663162+00:00
-- url     : https://prove2.me/submissions/9fe823a6-fc93-4fa6-a93d-e6edde1e59f9

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_compact_secant
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_atomic_cash_summable
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_eligible_prepost
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
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
    ∀ ω, Summable (J ω) := by 
  dsimp only
  intro ω
  obtain ⟨K, hK, hsec⟩ := avram_locmoll_band_compact_secant g hg R
  have hs := avram_locmoll_band_atomic_cash_summable X x q hq.le D hD.1.1 ω (θ ω)
  apply (hs.mul_left (1 + K)).of_norm_bounded
  intro s
  split
  next he =>
    have hb := avram_locmoll_band_eligible_prepost X x C D hD δ R hxR θ hprefix ω s he.1 he.2
    have hd := dividendStrategy_le_rightLimit D hD.1.1 ω s
    have hdiff := hsec (x + X.X s ω - rightLimit D s ω) hb.2 (riskProcess X x D s ω) hb.1
    rw [show x + X.X s ω - rightLimit D s ω - riskProcess X x D s ω =
      -(rightLimit D s ω - D s ω) by unfold riskProcess; ring, abs_neg, abs_of_nonneg (sub_nonneg.mpr hd)] at hdiff
    simp only [if_pos he, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have ht := abs_add_le (rightLimit D s ω - D s ω) (g (x + X.X s ω - rightLimit D s ω) - g (riskProcess X x D s ω))
    rw [abs_of_nonneg (sub_nonneg.mpr hd)] at ht
    rw [add_sub_assoc]
    calc
      _ ≤ Real.exp (-(q * (s : ℝ))) * ((1 + K) * (rightLimit D s ω - D s ω)) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = _ := by ring
  next he => simp [he]
