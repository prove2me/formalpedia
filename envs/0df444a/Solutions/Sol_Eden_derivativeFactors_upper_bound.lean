-- Prove2me | solution 1 for Eden.derivativeFactors_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:51:20.546005+00:00
-- url     : https://prove2.me/submissions/7066263d-ec66-4bea-8496-0152e6444a89

import Definitions.Def_Eden_ExteriorCocycle
import Definitions.Def_Eden_FactorBounds
import Definitions.Def_Eden_IntegerGrowthBounds
import Theorems.Thm_Eden_radialAmplitude_upper_bound
import Theorems.Thm_Eden_planarAmplitude_upper_bound
import Theorems.Thm_P2M_Eden_radiusSq__nonneg_5272e4fb8458
import Theorems.Thm_P2M_Eden_radiusSq__nonneg_7729c3bfdb8d


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t)
    (p : PhaseSpace) (i : Fin 5) : derivativeFactors c t p i ≤ Real.exp (3 * t) := by
  fin_cases i
  · exact radialAmplitude_upper_bound ht (radiusSq₁_nonneg p)
  · exact planarAmplitude_upper_bound ht (radiusSq₁_nonneg p)
  · exact radialAmplitude_upper_bound ht (radiusSq₂_nonneg p)
  · exact planarAmplitude_upper_bound ht (radiusSq₂_nonneg p)
  · exact Real.exp_le_exp.mpr (by nlinarith)
end Eden
