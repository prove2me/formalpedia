-- Prove2me | solution 5 for AvramDividend.Classical.vcstar_global_C1_bv_positive_barrier
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:36:58.45801+00:00
-- url     : https://prove2.me/submissions/ac058fae-b1e0-46f1-b33b-a3e872f03d40
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_standing_bv_levy_absolutely_continuous
import Theorems.Thm_AvramDividend_Classical_bv_ac_esscher_continuous_renewal_density_representation
import Theorems.Thm_AvramDividend_Classical_vcstar_bv_global_C1_of_esscher_integrated_continuous_density

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

/-- Full positive-axis BV C1 barrier regularity reduces to the precise
continuous Esscher-renewal density theorem, retaining all Standing data. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hbv : X.BoundedVariation) :
    ContDiffOn ℝ 1 (vcstar W) (Ioi 0) := by
  have hac : X.ν ≪ volume :=
    standing_bv_levy_absolutely_continuous X hX hbv
  obtain ⟨φ, c, f, _hφ, _hroot, hcont, hint, hrepr⟩ :=
    bv_ac_esscher_continuous_renewal_density_representation
      X hX q hq W hW hbv hac
  have ha : 0 < (cstar W).toReal :=
    ENNReal.toReal_pos (ne_of_gt hcpos) (ne_of_lt hc)
  exact vcstar_bv_global_C1_of_esscher_integrated_continuous_density
    X hX q hq W f hW hbv ha φ c hcont hint hrepr
