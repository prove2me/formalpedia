-- Prove2me | solution 2 for AvramDividend.Classical.scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:29:12.795641+00:00
-- url     : https://prove2.me/submissions/2603d4e5-945f-49f3-8273-ef52c24e73ba

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_ac_esscher_continuous_renewal_density_representation
import Theorems.Thm_AvramDividend_Classical_scale_C1_of_esscher_integrated_continuous_density

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

/-- BV absolutely-continuous Lévy C1 reduces to continuous Esscher
renewal-density representation under the full Standing assumptions. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (hac : X.ν ≪ volume) :
    ContDiffOn ℝ 1 W (Ioi 0) := by
  obtain ⟨φ, c, f, _hφ, _hroot, hcont, hint, hrepr⟩ :=
    bv_ac_esscher_continuous_renewal_density_representation
      X hX q hq W hW hbv hac
  exact scale_C1_of_esscher_integrated_continuous_density
    W f φ c hcont hint hrepr
