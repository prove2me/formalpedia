-- Prove2me | solution 1 for BlackScholesModel.call_upper_tail_spot_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T16:15:47.290226+00:00
-- url     : https://prove2.me/submissions/321f5163-eda9-4198-8cc6-957e124d3bf6

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Theorems.Thm_BlackScholesModel_dPlus_spot_tail_limits
import Theorems.Thm_BlackScholesModel_pdf_dPlus_dMinus_balance
import Theorems.Thm_BlackScholesModel_stdNormalPDF_tendsto_zero_atTop
import Theorems.Thm_BlackScholesModel_stdNormalCDF_upper_tail_le_pdf

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

/-- Weighted Gaussian tail vanishes, using Mills' bound and density balance. -/
theorem solution (K r σ τ : ℝ) (hK : 0 < K)
    (hσ : 0 < σ) (hτ : 0 < τ) :
    Tendsto (fun S => S * (1 - stdNormalCDF (dPlus S K r σ τ)))
      atTop (𝓝 0) := by
  have hp : Tendsto (fun S => dPlus S K r σ τ) atTop atTop :=
    (dPlus_spot_tail_limits K r σ τ hK hσ hτ).2
  have hm : Tendsto (fun S => dMinus S K r σ τ) atTop atTop := by
    have hshift : Tendsto (fun _ : ℝ => -(σ * Real.sqrt τ)) atTop
        (𝓝 (-(σ * Real.sqrt τ))) := tendsto_const_nhds
    convert hp.atTop_add hshift using 1 <;>
      first
      | rfl
      | (funext S; simp only [dMinus, sub_eq_add_neg])
  have hPDFminus : Tendsto
      (fun S => stdNormalPDF (dMinus S K r σ τ))
      atTop (𝓝 0) :=
    stdNormalPDF_tendsto_zero_atTop.comp hm
  have hright : Tendsto
      (fun S => K * Real.exp (-r * τ) *
        stdNormalPDF (dMinus S K r σ τ))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto
        (fun _ : ℝ => K * Real.exp (-r * τ))
        atTop (𝓝 (K * Real.exp (-r * τ)))).mul hPDFminus
  have hevent : ∀ᶠ S : ℝ in atTop,
      0 ≤ S * (1 - stdNormalCDF (dPlus S K r σ τ)) ∧
      S * (1 - stdNormalCDF (dPlus S K r σ τ)) ≤
        K * Real.exp (-r * τ) *
          stdNormalPDF (dMinus S K r σ τ) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ),
      hp.eventually_ge_atTop (1 : ℝ)] with S hS hplus
    obtain ⟨hnonneg, hMills⟩ :=
      stdNormalCDF_upper_tail_le_pdf (dPlus S K r σ τ) hplus
    constructor
    · exact mul_nonneg (le_of_lt hS) hnonneg
    · calc
        S * (1 - stdNormalCDF (dPlus S K r σ τ)) ≤
            S * stdNormalPDF (dPlus S K r σ τ) :=
          mul_le_mul_of_nonneg_left hMills (le_of_lt hS)
        _ = K * Real.exp (-r * τ) *
            stdNormalPDF (dMinus S K r σ τ) :=
          pdf_dPlus_dMinus_balance S K r σ τ hS hK hσ hτ
  exact squeeze_zero'
    (hevent.mono (fun S h => h.1))
    (hevent.mono (fun S h => h.2))
    hright
