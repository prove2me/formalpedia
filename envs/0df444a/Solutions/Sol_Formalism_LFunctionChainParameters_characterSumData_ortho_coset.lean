-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.ortho_coset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:33:59.67571+00:00
-- url     : https://prove2.me/submissions/c126ae33-a5fb-433f-8451-506ab2da8110

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_ortho
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_phi_card_ne_zero
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_card_G
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_natCard_eq_filter

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
open Classical
namespace Formalism.LFunctionChainParameters.characterSumData
theorem _root_.solution (I : AddSubgroup (E0 × H)) (h g : E0 × H) :
    (1 / ((PhiSet (H := H)).card : ℂ)) * ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * cosetMean I h ψ
      = if g - h ∈ I then 2 / (Nat.card I : ℂ) else 0 := by
  have hS : Nat.card I = (univ.filter (fun x => x ∈ I)).card := natCard_eq_filter I
  have hc : ((univ.filter (fun x => x ∈ I)).card : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Finset.card_ne_zero.mpr ⟨0, by simp⟩
  have e1 : ∀ ψ : AddChar (E0 × H) ℂ, cosetMean I h ψ
      = (∑ x ∈ univ.filter (fun x => x ∈ I), ψ (h + x)) / ((univ.filter (fun x => x ∈ I)).card : ℂ) :=
    fun ψ => rfl
  simp_rw [e1]
  have e2 : ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g)
        * ((∑ x ∈ univ.filter (fun x => x ∈ I), ψ (h + x)) / ((univ.filter (fun x => x ∈ I)).card : ℂ))
      = (∑ x ∈ univ.filter (fun x => x ∈ I), ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * ψ (h + x))
        / ((univ.filter (fun x => x ∈ I)).card : ℂ) := by
    rw [Finset.sum_comm, Finset.sum_div]
    refine Finset.sum_congr rfl (fun ψ _ => ?_)
    rw [mul_div_assoc', Finset.mul_sum]
  rw [e2]
  have e3 : ∀ x : E0 × H, (h + x = g) ↔ (x = g - h) := fun x => by
    rw [eq_sub_iff_add_eq, add_comm]
  simp_rw [ortho, e3]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hS]
  have hΦ := phi_card_ne_zero (H := H)
  split_ifs
  · rw [card_G]
    first
    | (field_simp; done)
    | (field_simp; ring)
  · simp
end Formalism.LFunctionChainParameters.characterSumData
