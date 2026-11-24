-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.highest_weight_dual_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:39:46.847739+00:00
-- url     : https://prove2.me/submissions/2d93af50-839e-4a2f-b10f-e935808f3c94

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_partial_sequence_antitone
import Theorems.Thm_Formalism_CohomologicalDescent_LD_partial_sequence_top_eq_zero
import Theorems.Thm_Formalism_CohomologicalDescent_LD_highest_weight_prod_leading_minors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_leading_minor_zero_eq_one
import Theorems.Thm_Formalism_CohomologicalDescent_LD_partial_sequence_dual
import Theorems.Thm_Formalism_CohomologicalDescent_LA_leading_minor_full_eq_det
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution {r : ℕ} (M : ℕ) (ν : Fin r → ℕ) (hν : Antitone ν) (hM : ∀ a, ν a ≤ M) :
    hw ℤ le_rfl (dualWt M ν) = genericDet ℤ r ^ (M - partialSumOfExponents ν 0) * ld3Q ν := by
  rcases r with _ | n
  · have h : genericDet ℤ 0 = 1 := by simp [genericDet]
    simp [hw, ld3Q, h]
  · have hle : ∀ s, partialSumOfExponents ν s ≤ M := by
      intro s
      unfold partialSumOfExponents
      split_ifs
      · exact hM _
      · exact Nat.zero_le _
    rw [highest_weight_prod_leading_minors, ld3Q, Finset.prod_range_succ, Finset.prod_range_succ]
    have e1 : leadingMinorPolynomial (n + 1) (n + 1) = genericDet ℤ (n + 1) := by
      unfold leadingMinorPolynomial
      rw [dif_pos le_rfl]
      exact leading_minor_full_eq_det ℤ _ rfl _ _
    have e2 : leadingMinorPolynomial (n + 1) (n + 1 - (n + 1)) = 1 := leading_minor_zero_eq_one _ _ (by omega)
    rw [e1, e2, one_pow, mul_one, partial_sequence_dual M ν n (by omega), partial_sequence_top_eq_zero, Nat.sub_zero,
      show n + 1 - (n + 1) = 0 by omega, mul_comm]
    congr 1
    rw [← Finset.prod_range_reflect
      (fun s => leadingMinorPolynomial (n + 1) (n + 1 - (s + 1)) ^ (partialSumOfExponents ν s - partialSumOfExponents ν (s + 1))) n]
    refine Finset.prod_congr rfl fun t ht => ?_
    have ht' := Finset.mem_range.mp ht
    rw [partial_sequence_dual M ν t (by omega), partial_sequence_dual M ν (t + 1) (by omega),
      show n + 1 - (n - 1 - t + 1) = t + 1 by omega, show n + 1 - (t + 1) = n - 1 - t + 1 by omega,
      show n + 1 - (t + 1 + 1) = n - 1 - t by omega]
    have h3 := hle (n - 1 - t)
    have h4 := partial_sequence_antitone ν hν (n - 1 - t)
    congr 1
    omega
end Formalism.CohomologicalDescent.LD
