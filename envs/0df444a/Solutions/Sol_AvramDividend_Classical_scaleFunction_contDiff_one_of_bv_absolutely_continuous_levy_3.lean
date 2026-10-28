-- Prove2me | solution 3 for AvramDividend.Classical.scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:30:19.72583+00:00
-- url     : https://prove2.me/submissions/ec93bc50-db8e-40d4-ad07-f635b5356a11

import Theorems.Thm_AvramDividend_Classical_bv_ac_esscher_continuous_renewal_density_representation
import Theorems.Thm_AvramDividend_Classical_scale_C1_of_esscher_integrated_continuous_density

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (hac : X.ν ≪ volume) :
    ContDiffOn ℝ 1 W (Ioi 0) := by
  obtain ⟨φ, c, f, hφ, hroot, hfcont, hfint, hrepresentation⟩ :=
    bv_ac_esscher_continuous_renewal_density_representation
      X hX q hq W hW hbv hac
  exact scale_C1_of_esscher_integrated_continuous_density
    W f φ c hfcont hfint hrepresentation
