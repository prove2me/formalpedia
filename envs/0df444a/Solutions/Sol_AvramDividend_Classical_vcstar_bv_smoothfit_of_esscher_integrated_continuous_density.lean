-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_bv_smoothfit_of_esscher_integrated_continuous_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:30:14.041492+00:00
-- url     : https://prove2.me/submissions/6a5a35e9-ae3f-4d9a-a08c-da891fcc0fc6

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_const_add_intervalIntegral
import Theorems.Thm_AvramDividend_Classical_esscher_untilt_contDiffOn_one_of_tilt_contDiffOn_one
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_bv_contDiff_one

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

/-- BV smooth fit follows from a continuous Esscher-renewal density. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W f : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hbv : X.BoundedVariation)
    (φ c : ℝ)
    (hcont : ContinuousOn f (Ioi (0 : ℝ)))
    (hint : ∀ x : ℝ, 0 < x → IntervalIntegrable f volume 0 x)
    (hrepr : ∀ x : ℝ, 0 < x →
      Real.exp (-(φ * x)) * W x =
        c + ∫ y in (0 : ℝ)..x, f y) :
    deriv (vcstar W) (cstar W).toReal = 1 := by
  let V : ℝ → ℝ := fun x => c + ∫ y in (0 : ℝ)..x, f y
  have hV : ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) :=
    contDiffOn_one_const_add_intervalIntegral f c hcont hint
  have hreg : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) := by
    apply esscher_untilt_contDiffOn_one_of_tilt_contDiffOn_one φ W V hV
    intro x hx
    exact (hrepr x hx).symm
  exact vcstar_deriv_one_of_bv_contDiff_one X hX q hq W hW hc hcpos hbv hreg
