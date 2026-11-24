-- Prove2me | solution 1 for Formalism.AtG.norm_height_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:47:15.711999+00:00
-- url     : https://prove2.me/submissions/645fe0d9-c876-4c53-a8c0-2eb45305b440

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
import Theorems.Thm_Formalism_DivisionValues_PlaceSumConjugation_lw_pos
import Theorems.Thm_Formalism_PairingDivisionLocalBalance_lw_nonneg
import Theorems.Thm_P2M_Formalism_DivisionValues_prod_formula__ad6919c95c2d


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
theorem _root_.solution : DisjointUnionFactorProduct := by
  intro K _ _ _ _ x dl Bδ hx hdl hden hB
  classical
  obtain ⟨hfin, hpf⟩ := Formalism.DivisionValues.prod_formula' K x hx
  have hc : (Fintype.card (InfinitePlace K) : ℝ) * 2 = (finrank ℚ K : ℝ) := by
    have h3 := IsTotallyComplex.finrank K
    have h4 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
    have h5 := IsTotallyComplex.nrRealPlaces_eq_zero K
    rw [h3, h4, h5]; push_cast; ring
  have hpos : (0 : ℝ) < finrank ℚ K := by exact_mod_cast finrank_pos
  have hcard : (Fintype.card (InfinitePlace K) : ℝ) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hc; linarith
  have hmean : ∀ φ : InfinitePlace K → ℝ,
      (2 / (finrank ℚ K : ℝ)) * ∑ v, φ v = (∑ v, φ v) / Fintype.card (InfinitePlace K) := by
    intro φ
    rw [← hc]
    field_simp
  have hsupp : ∀ w, w ∉ hfin.toFinset → ((vw w x : ℤ) : ℝ) = 0 := by
    intro w hw
    have h0 : lw w * (vw w x : ℝ) = 0 := by
      by_contra hne
      exact hw (hfin.mem_toFinset.2 hne)
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h (Formalism.DivisionValues.PlaceSumConjugation.lw_pos w).ne'
    · exact h
  have hsum : ∑ w ∈ hfin.toFinset, lw w * (vw w x : ℝ) =
      (∑ v : InfinitePlace K, Real.log ‖v.embedding x‖) / Fintype.card (InfinitePlace K) := by
    rw [← hmean, hpf, finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by simp)]
  obtain ⟨_, _, h3⟩ := Formalism.ValuationGridEstimates.height_bound_alt (Pl K) (InfinitePlace K) (fun w => lw w)
    (fun w => (vw w x : ℝ)) dl (fun v => ‖v.embedding x‖) hfin.toFinset Bδ
    (fun w => Formalism.PairingDivisionLocalBalance.lw_nonneg w) hsupp hsum
  have h4 := h3 hdl hden hB hfin.toFinset
  have hsub : (Function.support fun w : Pl K => lw w * |((vw w x + 0 : ℤ) : ℝ)|) ⊆
      (hfin.toFinset : Set (Pl K)) := by
    intro w hw
    by_contra hne
    apply hw
    have := hsupp w hne
    simp only [add_zero]
    rw [this, abs_zero, mul_zero]
  refine ⟨(hfin.toFinset.finite_toSet).subset hsub, ?_⟩
  rw [finsum_eq_sum_of_support_subset _ hsub]
  unfold Formalism.PairingDivisionLocalBalance.meanInf
  rw [hmean]
  simpa only [add_zero] using h4
end Formalism.AtG
