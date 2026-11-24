-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.cofactor_cofactor_variable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:34:45.304462+00:00
-- url     : https://prove2.me/submissions/3cf33436-a14b-42e6-9bbe-b2e6c09b82f8

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_cofactor_of_variable
import Theorems.Thm_Formalism_CohomologicalDescent_LD_cofactor_map_generic_matrix
import Theorems.Thm_Formalism_CohomologicalDescent_LD_adjugate_adjugate_smul
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
theorem _root_.solution (r : ℕ) (v : Fin r × Fin r) :
    genericDet ℤ r * cofMap r (cofMap r (X v)) = genericDet ℤ r ^ (r - 1) * X v := by
  obtain ⟨a, s⟩ := v
  have h1 : cofMap r (cofMap r (X (a, s))) = (genericMatrix' ℤ r).adjugate.adjugate a s := by
    rw [cofactor_of_variable]
    have h2 : cofMap r ((genericMatrix' ℤ r).adjugate (Fin.rev s) (Fin.rev a)) =
        (cofMap r).mapMatrix (genericMatrix' ℤ r).adjugate (Fin.rev s) (Fin.rev a) := rfl
    rw [h2, AlgHom.map_adjugate, cofactor_map_generic_matrix, Matrix.adjugate_submatrix_equiv_self, ← Matrix.adjugate_transpose]
    simp
  have h3 := congrFun (congrFun (adjugate_adjugate_smul (genericMatrix' ℤ r)) a) s
  rw [Fintype.card_fin] at h3
  rw [h1]
  exact h3
end Formalism.CohomologicalDescent.LD
