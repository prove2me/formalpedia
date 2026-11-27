-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_band_secant_dct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:43:09.572915+00:00
-- url     : https://prove2.me/submissions/58a16f1c-f0de-4a67-b359-e3fc14dfd26f

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_secant_tendsto
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    (μ : Measure ℝ) (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (a b c : ℕ → ℝ → ℝ) (A B E : ℝ → ℝ) (K : ℝ)
    (horder : ∀ᵐ t ∂μ, B t ≤ A t ∧ ∀ n, b n t ≤ a n t)
    (hends : ∀ᵐ t ∂μ, Tendsto (fun n => a n t) atTop (𝓝 (A t)) ∧
      Tendsto (fun n => b n t) atTop (𝓝 (B t)) ∧
      Tendsto (fun n => c n t) atTop (𝓝 (E t))) :
    let Q : ℝ → ℝ → ℝ := fun a b => if a = b then deriv g a else (g a - g b) / (a - b)
    let F : ℕ → ℝ → ℝ := fun n t => E t - c n t * Q (a n t) (b n t)
    let L : ℝ → ℝ := fun t => E t * (1 - Q (A t) (B t))
    (∀ n, AEStronglyMeasurable (F n) μ) →
    Integrable (fun _ : ℝ => K) μ →
    (∀ n, ∀ᵐ t ∂μ, ‖F n t‖ ≤ K) →
    Tendsto (fun n => ∫ t, F n t ∂μ) atTop (𝓝 (∫ t, L t ∂μ)) := by 
  dsimp only
  intro hm hK hbound
  apply tendsto_integral_of_dominated_convergence (fun _ : ℝ => K) hm hK hbound
  filter_upwards [horder, hends] with t ho he
  have hs := avram_locmoll_band_secant_tendsto g hg (fun n => a n t) (fun n => b n t)
    (A t) (B t) ho.2 ho.1 he.1 he.2.1
  have hconst : Tendsto (fun _ : ℕ => E t) atTop (𝓝 (E t)) := tendsto_const_nhds
  have ht := hconst.sub (he.2.2.mul hs)
  simpa only [mul_sub, mul_one] using ht
