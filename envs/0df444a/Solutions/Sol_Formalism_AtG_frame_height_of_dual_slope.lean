-- Prove2me | solution 1 for Formalism.AtG.frame_height_of_dual_slope
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:47:11.872218+00:00
-- url     : https://prove2.me/submissions/98b2b1dd-7eb9-4948-9508-19475658116f

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
theorem _root_.solution (hd : DualLatticeMinimalSlope) : FrameTheoremHeightNumber := by
  intro K _ _ _ _ D hD XE hXE R1 HH0 sF logκ lam0 c p2 ps bb hR1 h0 h1 hs hc hlam hbb hp
  have : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  have e := hd K (Fin D → K) (Fin D) (Pi.basisFun K (Fin D)) XE hXE R1
    (Submodule.IsLattice.fg (self := hR1)) (Submodule.IsLattice.span_eq_top (self := hR1))
  rw [e]
  refine ⟨?_, le_max_of_le_left hbb, max_le ?_ ?_⟩
  · have := le_max_right bb (sF + muMaxDef (Pi.basisFun K (Fin D)) XE R1)
    linarith
  · nlinarith
  · have : c * lam0 ≤ c * bb := mul_le_mul_of_nonneg_left hlam hc
    nlinarith
end Formalism.AtG
