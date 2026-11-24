-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.colour_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:34:10.129687+00:00
-- url     : https://prove2.me/submissions/1953e717-da7d-4854-acc5-b6c817d1190a

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_conj_eq_neg
import Theorems.Thm_P2M_Formalism_LFunctionChainParameters_characterSumData_PB_chC_apply__06e97235fe62
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_chC_neg
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_mul_chC_eq_zero_iff
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_chC_ne_zero
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_card_G
import Theorems.Thm_Formalism_D5_Bal_chC_ne_zero
import Theorems.Thm_Formalism_D5_Bal_chC_neg
import Theorems.Thm_Formalism_D5_Bal_mul_chC_eq_zero_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.characterSumData
open Formalism Formalism.D5
open PB
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.characterSumData
theorem _root_.solution : ColourSum (H := H) := by
  intro ψ
  have hneg : ∀ F : E0 × H → ℂ, ∑ g : E0 × H, F (-g) = ∑ g : E0 × H, F g :=
    fun F => Fintype.sum_equiv (Equiv.neg _) _ _ (fun _ => rfl)
  have hind : ∀ g : E0 × H, (if ¬ InPhi g then (1 : ℂ) else 0) = (1 - chC g) / 2 := by
    intro g
    rw [chC_apply']
    by_cases h : g.1.1 = 0
    · rw [if_pos h, if_neg (show ¬¬InPhi g from not_not.2 h)]
      ring
    · rw [if_neg h, if_pos (show ¬InPhi g from h)]
      ring
  have e1 : ∀ g : E0 × H, (if ¬ InPhi g then starRingEnd ℂ (ψ g) else 0)
      = (starRingEnd ℂ (ψ g) - chC g * starRingEnd ℂ (ψ g)) / 2 := by
    intro g
    rw [← boole_mul, hind]
    ring
  have hA : ∑ g : E0 × H, starRingEnd ℂ (ψ g) = if ψ = 0 then (Fintype.card (E0 × H) : ℂ) else 0 := by
    simp_rw [conj_eq_neg]
    rw [hneg (⇑ψ), AddChar.sum_eq_ite]
  have hB : ∑ g : E0 × H, chC g * starRingEnd ℂ (ψ g)
      = if ψ = chC then (Fintype.card (E0 × H) : ℂ) else 0 := by
    have h4 : ∀ g : E0 × H, chC g * starRingEnd ℂ (ψ g) = ((ψ * chC : AddChar (E0 × H) ℂ)) (-g) := by
      intro g
      rw [AddChar.mul_apply, conj_eq_neg, ← chC_neg, mul_comm]
    simp_rw [h4]
    rw [hneg (⇑(ψ * chC : AddChar (E0 × H) ℂ)), AddChar.sum_eq_ite]
    simp only [mul_chC_eq_zero_iff]
  rw [Finset.sum_filter]
  simp_rw [e1]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, hA, hB, card_G]
  have hne := chC_ne_zero (H := H)
  by_cases h0 : ψ = 0
  · have h1 : ¬ ψ = chC := fun h => hne (h ▸ h0)
    simp only [if_pos h0, if_neg h1]
    ring
  · by_cases h1 : ψ = chC
    · simp only [if_neg h0, if_pos h1]
      ring
    · simp only [if_neg h0, if_neg h1]
      ring
end Formalism.LFunctionChainParameters.characterSumData
