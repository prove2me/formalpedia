-- Prove2me | solution 1 for Formalism.D5.sum_H
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:54.405344+00:00
-- url     : https://prove2.me/submissions/86aecbdc-3748-47de-9e37-3a4635f3be27

import Definitions.Def_Formalism_ThickAverageLoss_ParametersAveragedDifferenceBound
import Definitions.Def_Formalism_ThickAverageLoss_PartnersToFactorsAt
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
open Classical
namespace Formalism.D5
theorem _root_.solution (ψ : AddChar (E0 × H) ℂ) :
    ∑ h : H, ψ ((0, 0), h) = if TrivH ψ then (Fintype.card H : ℂ) else 0 := by
  split_ifs with hT
  · have hT' : ∀ h : H, ψ ((0, 0), h) = 1 := hT
    simp [hT']
  · have hT' : ¬ ∀ h : H, ψ ((0, 0), h) = 1 := hT
    push_neg at hT'
    obtain ⟨h0, hh0⟩ := hT'
    have key : ψ ((0, 0), h0) * ∑ h : H, ψ ((0, 0), h) = ∑ h : H, ψ ((0, 0), h) := by
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.addLeft h0) _ _ (fun h => ?_)
      show ψ ((0, 0), h0) * ψ ((0, 0), h) = ψ ((0, 0), h0 + h)
      rw [← AddChar.map_add_eq_mul]
      congr 1
      all_goals (ext <;> simp)
    have h2 : (ψ ((0, 0), h0) - 1) * ∑ h : H, ψ ((0, 0), h) = 0 := by
      rw [sub_mul, key, one_mul, sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd (sub_eq_zero.mp h3) hh0
    · exact h3
end Formalism.D5
