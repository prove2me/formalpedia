-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ThmSFull_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:36.772249+00:00
-- url     : https://prove2.me/submissions/b8ce82e7-3352-4cf8-9146-aaa7dc95394a

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormLiftLeOne
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_norm_lift_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (hB : BetaIsG) (hK : CyclicPowerClassOfExpEquiv) (hM : MapSimeq) : ThmSFull := by
  intro K0 K _ _ _ _ _ _ _ j p ν r0 r1 _ σ hj hU hζ F hF be hbe
  obtain ⟨c, hc, hσc, hsim⟩ := hB K0 p σ hU hζ F hF be hbe
  refine ⟨c, hc, hσc, ?_⟩
  intro om oms ϖ μ U0 Φ hϖ hom hμ0 hμ hU0 hΦ0 hΦ
  have hpK : ‖(p : K)‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast j p, hj]
    exact hU.2.2.1
  have hσc1 : ‖σ c‖ ≤ 1 := norm_lift_le_one hU hc
  obtain ⟨hMs, hMG⟩ := hM K0 K (Fin 2) j hj
  refine hK K p ν r0 r1 om oms (j c) (j (σ c)) ϖ μ U0 Φ (MvPowerSeries.map j be) hU.1 hpK hϖ
    hom (by rw [hj]; exact hc) (by rw [hj]; exact hσc1) hμ0 hμ hU0 hΦ0 hΦ ?_
  rw [← hMG p c (σ c)]
  exact hMs _ _ hsim
end Formalism.InvariantFactorPaths.G7
