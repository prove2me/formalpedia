-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_eq_scaledW_on_Iic_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:32:11.111652+00:00
-- url     : https://prove2.me/submissions/c6d946fa-6aca-4851-be7b-5e4100a267f7

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_scaledW_le_cstar_of_support

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- Reuse the proved support-aware scaled-scale identity on the full
left-closed interval below the finite real representation of cstar. -/
theorem solution
    (W : ℝ → ℝ) (hnegative : ∀ z : ℝ, z < 0 → W z = 0)
    (z : ℝ) (hz : z ≤ (cstar W).toReal) :
    vcstar W z =
      divE (W z) (scaleDeriv W (cstar W).toReal) := by
  exact vcstar_eq_scaledW_le_cstar_of_support W hnegative z hz
