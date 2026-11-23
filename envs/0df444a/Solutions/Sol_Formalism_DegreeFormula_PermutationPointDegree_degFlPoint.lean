-- Prove2me | solution 1 for Formalism.DegreeFormula.PermutationPointDegree.degFlPoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:58.193201+00:00
-- url     : https://prove2.me/submissions/0c86918f-49a5-4004-b82f-fc9633aa8664

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PermExpInj
import Theorems.Thm_Formalism_DegreeFormula_PermutationPointDegree_permExp_inj
import Theorems.Thm_Formalism_DegreeFormula_PermutationPointDegree_sum_delta
import Theorems.Thm_Formalism_DegreeFormula_PermutationPointDegree_prod_negX

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.DegreeFormula Formalism.DegreeFormula.PermutationPointDegree
open Formalism.DegreeFormula
namespace Formalism.DegreeFormula.PermutationPointDegree
theorem _root_.solution : DegFlPoint := by
  intro ι _ _ N
  rw [prod_negX]
  unfold degFl
  rw [Finset.sum_eq_single (fun _ => 1)]
  · have hs : ∑ x : ι × Fin N, (N - 1 - (x.2 : ℕ)) = dimFl ι N := by
      rw [Fintype.sum_prod_type]
      simp [sum_delta, dimFl]
    have he : permExp (fun _ : ι => (1 : Equiv.Perm (Fin N))) =
        Finsupp.equivFunOnFinite.symm (fun x : ι × Fin N => N - 1 - (x.2 : ℕ)) := by
      ext x; simp [permExp]
    rw [he, coeff_C_mul, coeff_monomial, if_pos rfl, hs]
    simp [← pow_add, ← two_mul, pow_mul]
  · intro σ _ hσ
    have he : permExp (fun _ : ι => (1 : Equiv.Perm (Fin N))) =
        Finsupp.equivFunOnFinite.symm (fun x : ι × Fin N => N - 1 - (x.2 : ℕ)) := by
      ext x; simp [permExp]
    rw [coeff_C_mul, coeff_monomial, ← he, if_neg]
    · simp
    · intro h; exact hσ (permExp_inj _ _ h).symm
  · simp
end Formalism.DegreeFormula.PermutationPointDegree
