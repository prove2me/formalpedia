-- Prove2me | solution 1 for Formalism.FG.low_coeff_vector
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:58.308586+00:00
-- url     : https://prove2.me/submissions/85c6a82a-ecf3-42a2-ac64-b68accb21226

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffExpandEqZero
import Theorems.Thm_Formalism_FG_LowCoefficients_coeff_expand_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG
open Formalism.G
namespace Formalism.FG
theorem _root_.solution : Formalism.FG.LowCoeffV.{u, v, w} := by

  intro K _ _ p q hq σ hq2 ι _ M τ D hD N hN hlow j d hd
  have h1 := hD j d
  have h2 : MvPowerSeries.coeff d
      (∑ k, M j k • MvPowerSeries.expand q hq (MvPowerSeries.map σ (D k))) = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [map_smul, smul_eq_mul,
      LowCoefficients.coeff_expand_eq_zero q hq hq2 _ N hN (fun m hm => by rw [MvPowerSeries.coeff_map, hlow k m hm, map_zero]) d hd,
      mul_zero]
  rw [map_sub, map_smul, smul_eq_mul, h2, mul_zero, sub_zero] at h1
  exact h1
end Formalism.FG
