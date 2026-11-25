-- Prove2me | solution 1 for Formalism.AtG.grid_square_bound_cm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:20:16.330509+00:00
-- url     : https://prove2.me/submissions/b7096b9b-fcf4-4ad8-af64-e426fa68ee04

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
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_inv
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_mul
import Theorems.Thm_Formalism_PairingDivisionLocalBalance_vw_prod


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
theorem _root_.solution : SquareAtPlaceRatiosCM := by
  intro K _ _ _ w δ σ p q c0 c00 A A0 A0' P0 P1 P2 hc0 hc00 hA hA0 hA0' hP0 hP1 hP2 hcA hcA' hAA
    ub ua hu hub hua r hr
  have vmul := Formalism.DivisionValues.ValuationRepresentative.vw_mul w
  have vinv := Formalism.DivisionValues.ValuationRepresentative.vw_inv w
  have n1 : (∏ j ∈ range q, ub j) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => (hu j).1
  have n2 : (∏ i ∈ range p, ua i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => (hu j).2
  have n3 : c0 / c00 ≠ 0 := div_ne_zero hc0 hc00
  have e1 : vw w r = (∑ j ∈ range q, vw w (ub j)) + (∑ i ∈ range p, vw w (ua i)) +
      (vw w c0 - vw w c00) + vw w P1 - vw w P2 := by
    rw [hr, vmul _ _ (mul_ne_zero (mul_ne_zero (mul_ne_zero n1 n2) n3) hP1) (inv_ne_zero hP2),
      vmul _ _ (mul_ne_zero (mul_ne_zero n1 n2) n3) hP1, vmul _ _ (mul_ne_zero n1 n2) n3,
      vmul _ _ n1 n2, vinv, div_eq_mul_inv, vmul _ _ hc0 (inv_ne_zero hc00), vinv,
      Formalism.PairingDivisionLocalBalance.vw_prod w _ _ (fun j _ => (hu j).1), Formalism.PairingDivisionLocalBalance.vw_prod w _ _ (fun j _ => (hu j).2)]
    ring
  have e2 : vw w (P0 * P1 * P2⁻¹) = vw w P0 + vw w P1 - vw w P2 := by
    rw [vmul _ _ (mul_ne_zero hP0 hP1) (inv_ne_zero hP2), vmul _ _ hP0 hP1, vinv]; ring
  have e3 : vw w P0 = vw w A - vw w A0 := by
    rw [← hAA, div_eq_mul_inv, vmul _ _ hA (inv_ne_zero hA0), vinv]; ring
  have b1 : ((∑ j ∈ range q, vw w (ub j) : ℤ) : ℝ) ≤ q * σ := by
    push_cast
    calc ∑ j ∈ range q, (vw w (ub j) : ℝ) ≤ ∑ _j ∈ range q, σ :=
          Finset.sum_le_sum fun j hj => hub j (Finset.mem_range.1 hj)
      _ = q * σ := by simp
  have b2 : ((∑ i ∈ range p, vw w (ua i) : ℤ) : ℝ) ≤ p * σ := by
    push_cast
    calc ∑ j ∈ range p, (vw w (ua j) : ℝ) ≤ ∑ _j ∈ range p, σ :=
          Finset.sum_le_sum fun j hj => hua j (Finset.mem_range.1 hj)
      _ = p * σ := by simp
  rw [e1, e2, e3]
  push_cast at b1 b2 ⊢
  linarith
end Formalism.AtG
