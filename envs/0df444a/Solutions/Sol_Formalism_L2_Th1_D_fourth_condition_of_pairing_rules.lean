-- Prove2me | solution 1 for Formalism.L2.Th1.D.fourth_condition_of_pairing_rules
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:05:33.394939+00:00
-- url     : https://prove2.me/submissions/a56659bc-7df1-4caf-9b0e-d7acc7f63fe2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionHypothesesOfConditions
import Theorems.Thm_Formalism_L2_Th1_D_B4_linEL_congr
import Theorems.Thm_Formalism_L2_Th1_D_B4_linOL_congr
import Theorems.Thm_Formalism_L2_Th1_D_B4_linEL_add
import Theorems.Thm_Formalism_L2_Th1_D_B4_linOL_add
import Theorems.Thm_Formalism_L2_Th1_D_B4_subst_first_coordinate
import Theorems.Thm_Formalism_L2_Th1_D_B4_subst_first_sum_even
import Theorems.Thm_Formalism_L2_Th1_D_B4_subst_first_odd
import Theorems.Thm_Formalism_L2_Th1_D_B4_subst_second_even
import Theorems.Thm_Formalism_L2_Th1_D_B4_subst_second_odd
import Theorems.Thm_Formalism_L2_Th1_D_B4_subst_s1Prime_even
import Theorems.Thm_Formalism_L2_Th1_D_B4_subst_s1Prime_odd
import Theorems.Thm_Formalism_L2_Th1_D_B4_subst_s2Prime_even
import Theorems.Thm_Formalism_L2_Th1_D_B4_subst_s2Prime_odd
import Theorems.Thm_Formalism_L2_Th1_D_B4_simeq_sum
import Theorems.Thm_Formalism_L2_Th1_D_B4_simeq_sub_zero
import Theorems.Thm_Formalism_L2_Th1_D_B4_subst_letter_til
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_cc_letterLog
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_constantCoeff_substOne
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_constantCoeff_substTwo
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_constantCoeff_substZero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_simeq_sum
import Theorems.Thm_P2M_Formalism_DworkPowerSeriesWeights_Transfer_constantCoeff_substOne__6454fc9e7ded
import Theorems.Thm_P2M_Formalism_DworkPowerSeriesWeights_Transfer_constantCoeff_substTwo__588f1fb17580


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus BHyp NoLowBidegree letterLog de1 de2 s0 s1 s2 s1' s2' V2 degE)
open Formalism.InvariantFactorPaths.G7 (Simeq DivAB UnrOK IsLawOfLog)
open MvPowerSeries (subst HasSubst constantCoeff)
open B4
namespace Formalism.L2.Th1.D
theorem _root_.solution (hP : PairRules) (hS : SubstTil) (hI : ShiftIP) (hL : LetterShift) : TorusSumCoboundaryCondition := by
  intro K _ _ _ l d _ σ hU hd hev F hF be0 hF1 ι _ om oms hO
  have hl : 2 ≤ l := hU.1.two_le
  have hc : ∀ x : V2 d, constantCoeff (letterLog (K := K) l x) = 0 :=
    Formalism.DworkPowerSeriesWeights.Transfer.cc_letterLog l
  have hLL : HasSubst (letterLog (K := K) (d := d) l) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hc
  obtain ⟨hsh, -, -⟩ := hL K l d σ hU.1
  have ipE : ∀ (b : Bool) (r : ι),
      IP l σ (linEL σ (oms r) fun s : ZMod d => letterLog (K := K) l (b, s)) := fun b r =>
    (hI K l d σ hU hev (V2 d) _ (hsh b) (oms r) (hO.1 r).2 (hO.2 r).2).1
  have ipO : ∀ (b : Bool) (r : ι),
      IP l σ (linOL σ (om r) fun s : ZMod d => letterLog (K := K) l (b, s)) := fun b r =>
    (hI K l d σ hU hev (V2 d) _ (hsh b) (om r) (hO.1 r).1 (hO.2 r).1).2
  obtain ⟨p1, p2, -⟩ := hP K l σ hU F hF be0 hF1 (V2 d)
  constructor
  · unfold de1
    rw [MvPowerSeries.subst_sub hLL, MvPowerSeries.subst_sub hLL,
      subst_letter_til hS l d σ hl be0 ι om oms s1 Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substOne,
      subst_letter_til hS l d σ hl be0 ι om oms s0 Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substZero,
      subst_letter_til hS l d σ hl be0 ι om oms s2 Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substTwo,
      sub_sub, ← Finset.sum_add_distrib]
    refine simeq_sub_zero (simeq_sum _ _ _ fun r _ => ?_)
    rw [linEL_congr σ (oms r) (L' := fun s => letterLog (K := K) l (false, s) +
        letterLog (K := K) l (true, s)) (fun s hs => subst_first_sum_even hLL hs), linEL_add,
      linOL_congr σ (om r) (L' := fun s => letterLog (K := K) l (false, s))
        (fun s hs => subst_first_odd hLL hs),
      linEL_congr σ (oms r) (L' := fun s => letterLog (K := K) l (false, s))
        (fun s _ => subst_first_coordinate hLL s),
      linOL_congr σ (om r) (L' := fun s => letterLog (K := K) l (false, s))
        (fun s _ => subst_first_coordinate hLL s),
      linEL_congr σ (oms r) (L' := fun s => letterLog (K := K) l (true, s))
        (fun s hs => subst_second_even hLL hs),
      linOL_congr σ (om r) (L' := fun s => letterLog (K := K) l (false, s))
        (fun s hs => subst_second_odd hLL hs)]
    exact p1 _ _ _ (ipE false r) (ipE true r) (ipO false r)
  · unfold de2
    rw [MvPowerSeries.subst_sub hLL, MvPowerSeries.subst_sub hLL,
      subst_letter_til hS l d σ hl be0 ι om oms s1' Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substOne',
      subst_letter_til hS l d σ hl be0 ι om oms s0 Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substZero,
      subst_letter_til hS l d σ hl be0 ι om oms s2' Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substTwo',
      sub_sub, ← Finset.sum_add_distrib]
    refine simeq_sub_zero (simeq_sum _ _ _ fun r _ => ?_)
    rw [linEL_congr σ (oms r) (L' := fun s => letterLog (K := K) l (false, s))
        (fun s hs => subst_s1Prime_even hLL hs),
      linOL_congr σ (om r) (L' := fun s => letterLog (K := K) l (false, s) +
        letterLog (K := K) l (true, s)) (fun s hs => subst_s1Prime_odd hLL hs), linOL_add,
      linEL_congr σ (oms r) (L' := fun s => letterLog (K := K) l (false, s))
        (fun s _ => subst_first_coordinate hLL s),
      linOL_congr σ (om r) (L' := fun s => letterLog (K := K) l (false, s))
        (fun s _ => subst_first_coordinate hLL s),
      linEL_congr σ (oms r) (L' := fun s => letterLog (K := K) l (false, s))
        (fun s hs => subst_s2Prime_even hLL hs),
      linOL_congr σ (om r) (L' := fun s => letterLog (K := K) l (true, s))
        (fun s hs => subst_s2Prime_odd hLL hs)]
    exact p2 _ _ _ (ipE false r) (ipO false r) (ipO true r)
end Formalism.L2.Th1.D
