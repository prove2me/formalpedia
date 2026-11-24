-- Prove2me | solution 1 for Formalism.AtG.height_h0_of_grid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:47:13.30705+00:00
-- url     : https://prove2.me/submissions/faa3a6e6-d9bc-4d82-beb3-6cc029fee9c7

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
theorem _root_.solution (hG : GridHeightBound) (hF : LargestSlopeLatticeFrames) : PassageSizeHypothesis := by
  intro K W κ _ _ _ _ _ _ _ _ _ _ D hD XE kap b' X' hXE hkap hX' R M Ψ T a dF EM hInf BF p2 bb
    hR hM hM0 hΨ hincl hEM hh hBF Sq m N dl S Se N0 rr zA zA' zT zTd gT ch dd hh' yy S0 cc ee qq
    B BN0 Bδ ha hdl hS hSe hrr hdd hddN hyy hcc hsq hHA hHT hHTd hBN0 hBδ hsize
  have hg := hG K Sq m N dl S Se N0 rr zA zA' zT zTd gT ch dd hh' yy S0 cc ee qq B BN0 Bδ T
    hdl hS hSe hrr hdd hddN hyy hcc hsq hHA hHT hHTd hBN0 hBδ
  have h := hF K W κ D hD XE kap b' X' hXE hkap hX' R M Ψ T a (fun w => ∏ ij, rr w ij) dF EM hInf
    (gridBudget m N B BN0 Bδ S0 ee qq) BF hR hM hM0 hΨ hincl ha hEM hh hg hBF
  linarith
end Formalism.AtG
