-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_band_atom_endpoint_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:59:43.999531+00:00
-- url     : https://prove2.me/submissions/a09c987a-c3b2-41d3-b50f-6ce67e38722d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_preruin_postpayment_nonnegative
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
    ∀ ω s, J ω s ≤ if s = θ ω then δ else 0 := by 
  classical
  dsimp only
  intro ω s
  by_cases he : s ≤ θ ω ∧ (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω)
  · rw [if_pos he]
    have hb := dividendStrategy_le_rightLimit D hD.1.1 ω s
    have hpos := avram_p4_e_localise_preruin_postpayment_nonnegative X x C D hD ω s he.2
    let a := riskProcess X x D s ω
    let b := x + X.X s ω - rightLimit D s ω
    have hab : b ≤ a := by
      change x + X.X s ω - rightLimit D s ω ≤ x + X.X s ω - D s ω
      linarith
    have hdiff : rightLimit D s ω - D s ω = a - b := by
      dsimp [a,b,riskProcess]; ring
    have hdisc : Real.exp (-(q * (s : ℝ))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [hq.le, show 0 ≤ (s : ℝ) from s.2])
    by_cases hs : s = θ ω
    · rw [if_pos hs, hdiff]
      change Real.exp (-(q * (s : ℝ))) * (a - b + g b - g a) ≤ δ
      have h := hLoss a b hpos hab
      calc
        _ ≤ Real.exp (-(q * (s : ℝ))) * δ :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
        _ ≤ δ := by nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hdisc)]
    · rw [if_neg hs, hdiff]
      change Real.exp (-(q * (s : ℝ))) * (a - b + g b - g a) ≤ 0
      have h := hSec a b (hprefix ω s (lt_of_le_of_ne he.1 hs)).1 hab
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith)
  · rw [if_neg he]
    split <;> linarith
