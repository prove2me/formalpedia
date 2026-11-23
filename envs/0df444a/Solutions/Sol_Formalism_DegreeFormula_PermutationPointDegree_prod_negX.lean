-- Prove2me | solution 1 for Formalism.DegreeFormula.PermutationPointDegree.prod_negX
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:45.551566+00:00
-- url     : https://prove2.me/submissions/9d234d9c-5b0f-4080-82c9-bfbf714bbb6b

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PermExpInj

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
theorem _root_.solution {ι : Type} [Fintype ι] {N : ℕ} (e : ι × Fin N → ℕ) :
    (∏ x : ι × Fin N, (-X x : MvPolynomial (ι × Fin N) ℝ) ^ (e x)) =
      C ((-1 : ℝ) ^ (∑ x, e x)) * monomial (Finsupp.equivFunOnFinite.symm e) 1 := by
  rw [Finset.prod_congr rfl (fun x _ => neg_pow (X x : MvPolynomial (ι × Fin N) ℝ) (e x)),
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, monomial_eq,
    Finsupp.prod_fintype _ _ (by intro i; simp)]
  simp only [Finsupp.equivFunOnFinite_symm_apply_apply, map_pow, map_neg, map_one, one_mul]
end Formalism.DegreeFormula.PermutationPointDegree
