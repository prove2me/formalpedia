-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.adjugate_entry_weighted_homog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:19:06.4564+00:00
-- url     : https://prove2.me/submissions/3b609bc6-4f4f-40c3-b568-449267170894

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
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
theorem _root_.solution (r : ℕ) (i j : Fin r) :
    IsWeightedHomogeneous (rowW r r) ((genericMatrix' ℤ r).adjugate i j) (fun c => if c = j then 0 else 1) := by
  classical
  rw [Matrix.adjugate_apply, Matrix.det_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  rw [← mem_weightedHomogeneousSubmodule]
  refine zsmul_mem ?_ _
  rw [mem_weightedHomogeneousSubmodule]
  have e : (fun c : Fin r => if c = j then 0 else 1) =
      ∑ k, (if σ k = j then (0 : Fin r → ℕ) else Pi.single (σ k) 1) := by
    rw [Equiv.sum_comp σ (fun c => if c = j then (0 : Fin r → ℕ) else Pi.single c 1)]
    funext c
    rw [Finset.sum_apply, Finset.sum_eq_single c]
    · split_ifs <;> simp
    · intro b _ hb
      split_ifs
      · rfl
      · simp [hb]
    · simp
  rw [e]
  refine IsWeightedHomogeneous.prod _ _ _ fun k _ => ?_
  by_cases h : σ k = j
  · rw [if_pos h, h, Matrix.updateRow_self, Pi.single_apply]
    split_ifs
    · exact isWeightedHomogeneous_one _ _
    · exact isWeightedHomogeneous_zero _ _ _
  · rw [if_neg h, Matrix.updateRow_ne h]
    exact isWeightedHomogeneous_X ℤ (rowW r r) _
end Formalism.CohomologicalDescent.LD
