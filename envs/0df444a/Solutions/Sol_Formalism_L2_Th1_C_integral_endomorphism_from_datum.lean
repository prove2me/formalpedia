-- Prove2me | solution 1 for Formalism.L2.Th1.C.integral_endomorphism_from_datum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:52:44.001513+00:00
-- url     : https://prove2.me/submissions/a822b0c2-b289-46ad-8326-69ffee61fe3c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntegralEndomorphismFromDatum
import Theorems.Thm_Formalism_L2_Th1_C_CompactOperatorsAlt_exists_mulBy_eq
import Theorems.Thm_Formalism_L2_Th1_C_CompactOperatorsAlt_ne_zero_of_isEndoR
import Theorems.Thm_Formalism_L2_Th1_C_velu_x_coordinate_integral
import Theorems.Thm_Formalism_L2_Th1_C_USideA_intPS_C
import Theorems.Thm_Formalism_L2_Th1_C_USideA_intPS_X
import Theorems.Thm_Formalism_L2_Th1_C_USideA_intPS_mul
import Theorems.Thm_Formalism_L2_Th1_C_veluXFromZ


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
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open CompactOperatorsAlt
namespace Formalism.L2.Th1.C
theorem _root_.solution : EndIntFromDatum := by
  intro K _ _ R e l linv A c0 ι _ neg xP w xs al albar hL hX hA h2 hD
  obtain ⟨hZ, hN, hw, hxs, hxP, hal, -, hr⟩ := hD
  have hal0 : al ≠ 0 := ne_zero_of_isEndoR hN
  obtain ⟨g, hg0, hvg⟩ := exists_mulBy_eq hL hal0
  have hV := veluXFromZ K e l linv A c0 ι neg xP w xs al hL hX hZ hw
  rw [hvg] at hV
  have hg : IntPS R g :=
    velu_x_coordinate_integral K R A g ι xs xP al _ hA hxs hxP hr hal hal0 h2 hg0 hV
  show IntPS R (mulBy l linv al)
  rw [hvg]
  exact USideA.intPS_mul (USideA.intPS_mul (USideA.intPS_C hal) USideA.intPS_X) hg
end Formalism.L2.Th1.C
