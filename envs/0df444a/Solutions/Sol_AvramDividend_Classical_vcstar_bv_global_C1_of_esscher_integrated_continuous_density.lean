-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_bv_global_C1_of_esscher_integrated_continuous_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:29:33.600858+00:00
-- url     : https://prove2.me/submissions/41483f63-92f8-4ac2-8862-4ee222688128

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_const_add_intervalIntegral
import Theorems.Thm_AvramDividend_Classical_esscher_untilt_contDiffOn_one_of_tilt_contDiffOn_one
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_bv
import Theorems.Thm_AvramDividend_Classical_vcstar_C1_of_scale_C1_tilt

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

/-- Continuous renewal density and BV Esscher tilt imply global C1 barrier fit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W f : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (hcpos : 0 < (cstar W).toReal)
    (φ c : ℝ)
    (hcont : ContinuousOn f (Ioi (0 : ℝ)))
    (hint : ∀ x : ℝ, 0 < x → IntervalIntegrable f volume 0 x)
    (hrepr : ∀ x : ℝ, 0 < x →
      Real.exp (-(φ * x)) * W x =
        c + ∫ y in (0 : ℝ)..x, f y) :
    ContDiffOn ℝ 1 (vcstar W) (Ioi (0 : ℝ)) := by
  let V : ℝ → ℝ := fun x => c + ∫ y in (0 : ℝ)..x, f y
  have hV : ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) :=
    contDiffOn_one_const_add_intervalIntegral f c hcont hint
  have hreg : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) := by
    apply esscher_untilt_contDiffOn_one_of_tilt_contDiffOn_one φ W V hV
    intro x hx
    exact (hrepr x hx).symm
  obtain ⟨_, φ', hφ', hmono⟩ :=
    scaleFunction_tilted_positive_monotone_of_bv X hX q hq W hW hbv
  exact vcstar_C1_of_scale_C1_tilt X hX q hq W hW hcpos hreg
    ⟨φ', hφ', hmono⟩
