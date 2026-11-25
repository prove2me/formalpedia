-- Prove2me | solution 1 for Formalism.AtG.tower_height_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:18:18.968801+00:00
-- url     : https://prove2.me/submissions/fe847e0b-e222-4d4f-bd7a-3fb0fff0fa66

import Definitions.Def_Formalism_LocalToGlobal_ExponentGrids_ScaledCoordinatesValuationLemma
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_Height
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_SumValuationNat
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_ValAdd
import Definitions.Def_Formalism_TowerValuationBounds_TowerValuationProofs_SumAdditiveCharacterEqZero
import Definitions.Def_Lemmata_PlaneOverMembership_PlOverOfMem
import Definitions.Def_Formalism_LocalToGlobal_ExponentGrids_ExponentGridsProofs_FrameHeightOfDualSlope
import Theorems.Thm_Formalism_ValuationGridEstimates_tower_ratio_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw PlOver meanLog)
open Formalism.PairingDivisionLocalBalance (Pl wt HtLe meanInf)
open Formalism.HN (muMaxDef muMinDef htMap dualLat dualFrame)
noncomputable section
open Formalism Formalism.AtG
namespace Formalism.AtG
theorem _root_.solution : CoefficientRatioTowerFormula := by
  intro K F _ _ ι L L0 c u cb u0 p q e Ω Ω' hΩ hΩ' hL h1 h2 h3 h4 x y E r c0 c00 ub ua hr hc0 hc00
    hub hua hP1 hP2
  apply ι.injective
  rw [map_mul, map_mul, map_mul, map_mul, map_inv₀, map_div₀, map_prod, map_prod, map_prod, map_prod,
    hr, hc0, hc00, Formalism.ValuationGridEstimates.tower_ratio_bound F L L0 c u cb u0 p q e Ω Ω' hΩ hΩ' hL h1 h2 h3 h4,
    Finset.prod_congr rfl (fun j hj => hub j (Finset.mem_range.1 hj)),
    Finset.prod_congr rfl (fun i hi => hua i (Finset.mem_range.1 hi)),
    Finset.prod_congr rfl (fun k hk => hP1 k (Finset.mem_Icc.1 hk).1 (Finset.mem_Icc.1 hk).2),
    Finset.prod_congr rfl (fun k hk => hP2 k (Finset.mem_Icc.1 hk).1 (Finset.mem_Icc.1 hk).2)]
end Formalism.AtG
