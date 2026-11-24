-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ThmSUniform_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:28:38.097559+00:00
-- url     : https://prove2.me/submissions/7a0170a4-d114-4c84-af4b-e4dad6113118

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_ThmSUniform
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_OmegaOfTraceDuality
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
theorem _root_.solution (hB : BetaIsG) (hK : CyclicPowerClassOfExpEquiv) (hM : MapSimeq) : ThmSUniform := by
  intro K0 _ _ _ _ p σ hU hζ F hF be hbe
  obtain ⟨c, hc, hcc, hsim⟩ := hB K0 p σ hU hζ F hF be hbe
  refine ⟨c, hc, hcc, hsim, ?_⟩
  intro K _ _ _ j ν r0 r1 _ hj om oms ϖ μ U0 Φ hϖ hom hμ0 hμ hU0 hΦ0 hΦ
  obtain ⟨hmap, hGs⟩ := hM K0 K (Fin 2) j hj
  have hp : ‖(p : K)‖ = (p : ℝ)⁻¹ := by
    rw [← hU.2.2.1, ← hj (p : K0), map_natCast]
  have hsim' : Simeq (MvPowerSeries.map j be) (Gser p (j c) (j (σ c))) := by
    rw [← hGs p c (σ c)]
    exact hmap _ _ hsim
  have hjc : ‖j c‖ ≤ 1 := by rw [hj]; exact hc
  have hjc' : ‖j (σ c)‖ ≤ 1 := by rw [hj]; exact norm_lift_le_one hU hc
  exact hK K p ν r0 r1 om oms (j c) (j (σ c)) ϖ μ U0 Φ (MvPowerSeries.map j be) hU.1 hp hϖ hom
    hjc hjc' hμ0 hμ hU0 hΦ0 hΦ hsim'
end Formalism.InvariantFactorPaths.G7
