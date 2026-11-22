-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_root_drift_pos_no_standing_public
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T14:15:31.416164+00:00
-- url     : https://prove2.me/submissions/20003728-1b2c-4367-a480-e99751b9d600

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_root_drift_pos_linear_upper_fc6b

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

set_option autoImplicit false

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hBV : X.BoundedVariation) : 0 < X.drift :=
  (p2m81_bv_root_drift_pos_linear_upper_fc6b X q φ hq hφ hroot hBV).1
