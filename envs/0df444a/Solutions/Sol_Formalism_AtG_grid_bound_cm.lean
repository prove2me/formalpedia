-- Prove2me | solution 1 for Formalism.AtG.grid_bound_cm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:21:25.766629+00:00
-- url     : https://prove2.me/submissions/145f441e-29b8-4599-a4fd-4dcf700833ac

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
import Theorems.Thm_Formalism_AtG_partial_nat
import Theorems.Thm_Formalism_AtG_partial_ht
import Theorems.Thm_P2M_Formalism_AtG_lw_nonneg__115b3852fc51
import Theorems.Thm_Formalism_DivisionValues_PlaceSumConjugation_vw_nat_nonneg
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
theorem _root_.solution : GridHeightBoundCM := by
  intro K _ _ _ _ Sq m dl rr cf zA zA' yy S0 cc ee qq B Bδ Ex T I _ al x u y hne hyy hcc hsq hHt hδ hcm hEx0
  have hEx : ∑ w ∈ T, lw w * (vw w (∏ ij, cf w ij) : ℝ) ≤ Ex := by
    rw [Finset.sum_congr rfl (fun w hw => by rw [hcm w hw])]
    exact hEx0
  have hQ1 : ∀ s, ∑ w ∈ T, lw w * (vw w (qq s : K) : ℝ) ≤ Real.log (qq s) :=
    fun s => partial_nat K (qq s) T
  have hQ0 : ∀ s, 0 ≤ ∑ w ∈ T, lw w * (vw w (qq s : K) : ℝ) := fun s =>
    Finset.sum_nonneg fun w _ => mul_nonneg (lw_nonneg' w)
      (by exact_mod_cast Formalism.DivisionValues.PlaceSumConjugation.vw_nat_nonneg (qq s) w)
  have hAbs : ∀ z : K, HtLe (fun _ => 0) z B → ∑ w ∈ T, lw w * (vw w z : ℝ) ≤ B := by
    intro z hz
    refine le_trans (Finset.sum_le_sum fun w _ =>
      mul_le_mul_of_nonneg_left (le_abs_self _) (lw_nonneg' w)) ?_
    have := partial_ht hz T
    simpa using this
  have hone : ∀ ij, ∑ w ∈ T, lw w * ((vw w (zA ij) : ℝ) + (vw w (zA' ij) : ℝ) + 6 * dl w +
      yy ij * (2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ))) ≤
      2 * B + 6 * Bδ + 2 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s) := by
    intro ij
    have e1 : ∑ w ∈ T, lw w * ((vw w (zA ij) : ℝ) + (vw w (zA' ij) : ℝ) + 6 * dl w +
        yy ij * (2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ))) =
        (∑ w ∈ T, lw w * (vw w (zA ij) : ℝ)) + (∑ w ∈ T, lw w * (vw w (zA' ij) : ℝ)) +
        6 * (∑ w ∈ T, lw w * dl w) +
        yy ij * (2 * ∑ s ∈ S0, (cc s : ℝ) * ∑ w ∈ T, lw w * (vw w (qq s : K) : ℝ)) := by
      have e2 : ∑ w ∈ T, lw w * ((yy ij : ℝ) * (2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ))) =
          yy ij * (2 * ∑ s ∈ S0, (cc s : ℝ) * ∑ w ∈ T, lw w * (vw w (qq s : K) : ℝ)) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun w _ => by ring
      have e3 : ∑ w ∈ T, lw w * (6 * dl w) = 6 * ∑ w ∈ T, lw w * dl w := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun w _ => by ring
      rw [← e2, ← e3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun w _ => by ring
    have b3 : ∑ s ∈ S0, (cc s : ℝ) * ∑ w ∈ T, lw w * (vw w (qq s : K) : ℝ) ≤
        ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s) :=
      Finset.sum_le_sum fun s hs => mul_le_mul (by exact_mod_cast hcc s hs) (hQ1 s) (hQ0 s)
        (Nat.cast_nonneg _)
    have b4 : 0 ≤ ∑ s ∈ S0, (cc s : ℝ) * ∑ w ∈ T, lw w * (vw w (qq s : K) : ℝ) :=
      Finset.sum_nonneg fun s _ => mul_nonneg (Nat.cast_nonneg _) (hQ0 s)
    have b5 : (yy ij : ℝ) * (2 * ∑ s ∈ S0, (cc s : ℝ) * ∑ w ∈ T, lw w * (vw w (qq s : K) : ℝ)) ≤
        m * (2 * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s)) :=
      mul_le_mul (by exact_mod_cast hyy ij) (by linarith) (by linarith) (Nat.cast_nonneg _)
    rw [e1]
    have := hAbs _ (hHt ij).1
    have := hAbs _ (hHt ij).2
    have := hδ T
    linarith
  have hr : ∀ w, (vw w (∏ ij, rr w ij) : ℝ) = ∑ ij, (vw w (rr w ij) : ℝ) := by
    intro w
    rw [Formalism.PairingDivisionLocalBalance.vw_prod w _ _ (fun ij _ => (hne w ij).1)]; push_cast; rfl
  have hc : ∀ w, (vw w (∏ ij, cf w ij) : ℝ) = ∑ ij, (vw w (cf w ij) : ℝ) := by
    intro w
    rw [Formalism.PairingDivisionLocalBalance.vw_prod w _ _ (fun ij _ => (hne w ij).2)]; push_cast; rfl
  calc ∑ w ∈ T, lw w * (vw w (∏ ij, rr w ij) : ℝ)
      ≤ ∑ w ∈ T, (lw w * (∑ ij, ((vw w (zA ij) : ℝ) + (vw w (zA' ij) : ℝ) + 6 * dl w +
          yy ij * (2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ)))) +
          lw w * (vw w (∏ ij, cf w ij) : ℝ)) := by
        refine Finset.sum_le_sum fun w hw => ?_
        rw [hr, hc, ← mul_add, ← Finset.sum_add_distrib]
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ij _ => hsq w hw ij) (lw_nonneg' w)
    _ = (∑ ij, ∑ w ∈ T, lw w * ((vw w (zA ij) : ℝ) + (vw w (zA' ij) : ℝ) + 6 * dl w +
          yy ij * (2 * ∑ s ∈ S0, (cc s : ℝ) * (vw w (qq s : K) : ℝ)))) +
          ∑ w ∈ T, lw w * (vw w (∏ ij, cf w ij) : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
        congr 1
        exact Finset.sum_congr rfl fun w _ => by rw [Finset.mul_sum]
    _ ≤ (∑ _ij : Fin m × Fin m, (2 * B + 6 * Bδ + 2 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s))) +
          Ex := add_le_add (Finset.sum_le_sum fun ij _ => hone ij) hEx
    _ = (m : ℝ) ^ 2 * (2 * B + 6 * Bδ + 2 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s)) + Ex := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
end Formalism.AtG
