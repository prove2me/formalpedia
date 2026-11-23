-- Prove2me | solution 1 for AvramDividend.Classical.avram_b58_original_signed_B25_ae_pointwise_three_error_limits_pass_cash_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:57:43.237212+00:00
-- url     : https://prove2.me/submissions/d13b62f7-670e-4e21-bc84-2df25f6ff3bf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (F MG MJ : Ω → ℝ) (b : ℝ)
    (G J E : ℕ → Ω → ℝ)
    (hGlim : ∀ᵐ ω ∂P,
      Tendsto (fun k => G k ω) atTop (𝓝 (MG ω)))
    (hJlim : ∀ᵐ ω ∂P,
      Tendsto (fun k => J k ω) atTop (𝓝 (MJ ω)))
    (hElim : ∀ᵐ ω ∂P,
      Tendsto (fun k => E k ω) atTop (𝓝 (0 : ℝ)))
    (hCashAll : ∀ᵐ ω ∂P, ∀ k,
      F ω ≤ b + G k ω + J k ω + E k ω) :
    ∀ᵐ ω ∂P, F ω ≤ b + MG ω + MJ ω := by
  filter_upwards [hCashAll, hGlim, hJlim, hElim] with ω hAll hG hJ hE
  have hSum :
      Tendsto (fun k : ℕ => b + G k ω + J k ω + E k ω)
        atTop (𝓝 (b + MG ω + MJ ω)) := by
    convert ((tendsto_const_nhds.add hG).add hJ).add hE using 1 <;>
      simp
  exact ge_of_tendsto hSum
    (Filter.Eventually.of_forall (fun k => hAll k))
