-- Prove2me | solution 1 for Formalism.AtG.j3P2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:28:08.542999+00:00
-- url     : https://prove2.me/submissions/0b15f4e1-fd90-412b-ac1c-3c0723175d4d

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
theorem _root_.solution : UnitRatioAtPlace := by
  intro Sq m N S0 ee qq B BN0 Bδ BF EM hInf f bb LL CB CN Cδ Sg pM pI pB hbb h1 hB hN hδ hS hSg
    hEM hI hBF
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hNn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have a1 : 2 * (2 + 8 * (N : ℝ)) * B ≤ 2 * (2 + 8 * N) * (CB * f * bb * LL) :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have a2 : 2 * (N : ℝ) * (BN0 + 1) ≤ 2 * N * ((CN + 1) * (f * bb * LL)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have a3 : 4 * (m : ℝ) * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s) ≤ 4 * m * (Sg * bb) :=
    mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hSg (sub_nonneg.2 hbb)]) (by positivity)
  have g : gridBudget m N B BN0 Bδ S0 ee qq ≤ (m : ℝ) ^ 2 * (2 * (2 + 8 * N) * (CB * f * bb * LL) +
      2 * N * ((CN + 1) * (f * bb * LL)) + 6 * (Cδ * f * bb * LL) + 4 * m * (Sg * bb)) := by
    unfold gridBudget
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  calc EM + hInf + 2 * (gridBudget m N B BN0 Bδ S0 ee qq + BF)
      ≤ pM * bb + pI * bb + 2 * ((m : ℝ) ^ 2 * (2 * (2 + 8 * N) * (CB * f * bb * LL) +
        2 * N * ((CN + 1) * (f * bb * LL)) + 6 * (Cδ * f * bb * LL) + 4 * m * (Sg * bb)) + pB * bb) := by
        linarith
    _ = _ := by ring
end Formalism.AtG
