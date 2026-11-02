-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_infinite_cap_original_closed_horizon_dividend_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:35:42.236091+00:00
-- url     : https://prove2.me/submissions/ab5c6cfd-95a1-407b-950a-38d15c7a8503

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_infinite_cap_gradient_global_secant
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Infinite-cap complete initial-atom and diffuse/singular discounted Stieltjes budget at any pre-ruin horizon, with no reserve-interior hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z})
    (hw_grad : ∀ z : ℝ, 0 < z → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (⊤ : ℝ≥0∞) D)
    (ω : Ω) (T : ℝ≥0)
    (hPre : T = 0 ∨ (T : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal
        (w (x + X.X T ω) -
          w (x + X.X T ω - rightLimit D T ω)) := by
  have hAdmissible : IsAdmissible X x D := hD.1
  have hStrategy : IsDividendStrategy 𝓕 D := hAdmissible.1
  have hJump := hAdmissible.2 ω T hPre
  have hCover : rightLimit D T ω ≤ x + X.X T ω := by
    dsimp [riskProcess] at hJump
    linarith only [hJump]
  have hDnonneg : 0 ≤ D T ω := by
    have hm := hStrategy.2.1 ω (show (0 : ℝ≥0) ≤ T from zero_le)
    simpa only [hStrategy.1 ω] using hm
  have hRightNonneg : 0 ≤ rightLimit D T ω := le_trans hDnonneg
    (dividendStrategy_le_rightLimit D hStrategy ω T)
  have hOrder : x + X.X T ω - rightLimit D T ω ≤ x + X.X T ω := by
    linarith only [hRightNonneg]
  have hSec := avram_wave5_04b_infinite_cap_gradient_global_secant
    w hw_cont hw_smooth hw_grad
    (x + X.X T ω - rightLimit D T ω) (x + X.X T ω)
    (sub_nonneg.mpr hCover) hOrder
  have hDrop : rightLimit D T ω ≤
      w (x + X.X T ω) - w (x + X.X T ω - rightLimit D T ω) := by
    linarith only [hSec]
  exact (avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound
    q hq D hStrategy ω T).trans (ENNReal.ofReal_le_ofReal hDrop)
