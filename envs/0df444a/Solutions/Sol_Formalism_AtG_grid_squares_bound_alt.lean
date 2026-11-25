-- Prove2me | solution 1 for Formalism.AtG.grid_squares_bound_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:20:19.082694+00:00
-- url     : https://prove2.me/submissions/f21054cb-9fe3-4e2a-bbb3-496f8e99e520

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
import Theorems.Thm_Formalism_AtG_grid_bound_general
import Theorems.Thm_Formalism_AtG_grid_square_bound

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
theorem _root_.solution : GridSquaresHeightBound := by
  intro K _ _ _ _ Sq m N dl S Se N0 rr zA zA' zT zTd gT ch aa aa' dd hh pp qp ep yT EE c0 c00 AA ub ua
    S0 cc ee qq B BN0 Bδ W0 hdl hS hSe hrk hddN hyy hcc hrr hzT hzTd hyE hzA hc hu h2 hE hC hAA hU hr
    hHA hHT hHTd hBN0 hBδ
  refine grid_bound_general K Sq m N dl S Se N0 rr zA zA' zT zTd gT ch dd hh (fun ij => pp ij + qp ij) S0 cc ee qq
    B BN0 Bδ W0 hdl hS hSe hrr (fun ij => (hrk ij).2.2.1) hddN hyy hcc ?_ hHA hHT hHTd hBN0 hBδ
  intro w hw ij
  obtain ⟨r1, r2, r3, r4, r5⟩ := hrk ij
  exact grid_square_bound K w (aa ij) (aa' ij) (dd ij) (hh ij) (pp ij) (qp ij) (ep ij) r1 r2 r3 r4 r5
    (zT ij) (zTd ij (ch w)) (yT w ij) (EE w ij) (fun s => gT ij s w) S Se N0 (dl w)
    (2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ)) (fun l hl => (hS l hl).2)
    (fun s => ⟨hzT ij s, hzTd ij (ch w) s, (hyE w ij s).1, (hyE w ij s).2⟩)
    (h2 w hw ij) (hE w hw ij) (c0 w ij) (c00 w ij) (AA w ij) (zA ij) (zA' ij)
    (hc w ij).1 (hc w ij).2.1 (hc w ij).2.2 (hzA ij).1 (hzA ij).2 (hC w hw ij).1 (hC w hw ij).2
    (hAA w hw ij) (ub w ij) (ua w ij) (hu w ij) (fun j => (hU w hw ij j).1)
    (fun j => (hU w hw ij j).2) (rr w ij) (hr w hw ij)
end Formalism.AtG
