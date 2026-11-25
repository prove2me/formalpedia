-- Prove2me | solution 1 for Formalism.AtG.grid_lemma_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:16:15.507858+00:00
-- url     : https://prove2.me/submissions/ed74964f-d281-4d9f-9a51-87177e29522c

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
import Theorems.Thm_Formalism_AtG_valR_ne
import Theorems.Thm_Formalism_AtG_valR_ge
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_inv
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_star


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
theorem _root_.solution : ScaledCoordinatesValuationLemma := by
  intro K _ _ _ w ι κ _ X z z' gm c0 δ hc0 hz hi hi' hg A A' hA hA' hA0 hA'0
  have hconj : ∀ x : K, valR w ((starRingEnd K) x) = valR (Formalism.DivisionValues.conjPl w) x := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp
    · rw [valR_ne _ _ hx, valR_ne _ _ (by simpa using hx), starRingEnd_apply,
        Formalism.DivisionValues.ValuationRepresentative.vw_star]
  obtain ⟨k1, k2, k3, k4⟩ := Formalism.ValuationGridEstimates.lemma_c_gauss_sum K (valR w) (valR (Formalism.DivisionValues.conjPl w)) (starRingEnd K)
    hconj ι κ X z z' gm c0 δ hc0 hz
    (fun x hx k => ⟨valR_ge _ _ _ ((hi x hx k).imp id (·.1)), valR_ge _ _ _ ((hi x hx k).imp id (·.2)),
      valR_ge _ _ _ ((hi' x hx k).imp id (·.1)), valR_ge _ _ _ ((hi' x hx k).imp id (·.2))⟩)
    (fun x hx k l => valR_ge _ _ _ (hg x hx k l))
  have eA : (∑ x ∈ X, ∑ k, ∑ l, z x k * (starRingEnd K) (z x l) * gm x k l) = A := by
    rw [hA]; rfl
  have eA' : (∑ x ∈ X, ∑ k, ∑ l, z' x k * (starRingEnd K) (z' x l) * gm x k l) = A' := by
    rw [hA']; rfl
  rw [eA] at k1 k3
  rw [eA'] at k2 k4
  rw [valR_ne _ _ hc0, valR_ne _ _ hA0, ← WithTop.coe_add, WithTop.coe_le_coe] at k1
  rw [valR_ne _ _ (inv_ne_zero hc0), valR_ne _ _ hA'0, ← WithTop.coe_add, WithTop.coe_le_coe,
    Formalism.DivisionValues.ValuationRepresentative.vw_inv] at k2
  rw [valR_ne _ _ hA0, WithTop.coe_le_coe] at k3
  rw [valR_ne _ _ hA'0, WithTop.coe_le_coe] at k4
  push_cast at k2
  exact ⟨k1, k2, k3, k4⟩
end Formalism.AtG
