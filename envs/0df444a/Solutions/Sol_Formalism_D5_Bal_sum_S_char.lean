-- Prove2me | solution 1 for Formalism.D5.Bal.sum_S_char
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:13:39.515025+00:00
-- url     : https://prove2.me/submissions/70644c18-8f1b-49ef-965f-6af2b7777994

import Definitions.Def_Formalism_ThickAverageLoss_PartnersToFactorsAt
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Theorems.Thm_Formalism_D5_Bal_inPhi_add_topPl
import Theorems.Thm_Formalism_D5_Bal_card_G_eq
import Theorems.Thm_Formalism_D5_Bal_chC_neg
import Theorems.Thm_Formalism_D5_Bal_mul_chC_eq_zero_iff
import Theorems.Thm_Formalism_D5_Bal_sum_neg_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset ArithmeticFunction
noncomputable section
namespace Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
namespace Bal
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
private lemma ite_not_inPhi_eq_mul_one_sub_chC_div_two (Hs : CycHost H) (t : H) (g : E0 × H) (x : ℂ) :
    (if ¬ InPhi (g + topPl t) then x else 0) = x * ((1 - Hs.chC g) / 2) := by
  by_cases h : g.1.1 = 0
  · have hp : InPhi (g + topPl t) := (inPhi_add_topPl g t).mpr h
    rw [if_neg (not_not.mpr hp), Hs.7, h, sgn2, if_pos rfl]
    norm_num
    try ring
  · have hp : ¬ InPhi (g + topPl t) := fun h' => h ((inPhi_add_topPl g t).mp h')
    rw [if_pos hp, Hs.7, sgn2, if_neg h]
    norm_num
    try ring
end
end Bal
end Formalism.D5
end
end

set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
open Formalism.D5.Bal
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.D5.Bal
theorem _root_.solution (Hs : CycHost H) (t : H) (ψ : AddChar (E0 × H) ℂ) (hψ : ψ ≠ 0) :
    ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)), ψ (-g)
      = if ψ = Hs.chC then -((PhiSet (H := H)).card : ℂ) else 0 := by
  have e1 : ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)), ψ (-g)
      = ∑ g : E0 × H, ψ (-g) * ((1 - Hs.chC g) / 2) := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun g _ => ite_not_inPhi_eq_mul_one_sub_chC_div_two Hs t g (ψ (-g)))
  have hs0 : ∑ g : E0 × H, ψ (-g) = 0 :=
    (sum_neg_eq (fun g => ψ g)).trans (AddChar.sum_eq_zero_iff_ne_zero.mpr hψ)
  have hs1 : ∑ g : E0 × H, ψ (-g) * Hs.chC g = ∑ g : E0 × H, (ψ * Hs.chC) g := by
    calc ∑ g : E0 × H, ψ (-g) * Hs.chC g = ∑ g : E0 × H, (ψ * Hs.chC) (-g) :=
          Finset.sum_congr rfl (fun g _ => by rw [AddChar.mul_apply, chC_neg])
      _ = ∑ g : E0 × H, (ψ * Hs.chC) g := sum_neg_eq (fun g => (ψ * Hs.chC) g)
  have hsplit : ∑ g : E0 × H, ψ (-g) * ((1 - Hs.chC g) / 2)
      = (∑ g : E0 × H, ψ (-g) - ∑ g : E0 × H, ψ (-g) * Hs.chC g) / 2 := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl (fun g _ => by ring)
  rw [e1, hsplit, hs0, hs1]
  by_cases h : ψ = Hs.chC
  · have h' : ψ * Hs.chC = 0 := (mul_chC_eq_zero_iff Hs ψ).mpr h
    rw [h', if_pos h]
    simp only [AddChar.zero_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [card_G_eq]
    ring
  · have h' : ¬ ψ * Hs.chC = 0 := fun h'' => h ((mul_chC_eq_zero_iff Hs ψ).mp h'')
    rw [AddChar.sum_eq_zero_iff_ne_zero.mpr h', if_neg h]
    ring
end Formalism.D5.Bal
