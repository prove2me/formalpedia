-- Prove2me | solution 1 for Formalism.DegreeFormula.PPowSum.degree_permExp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:13:39.527804+00:00
-- url     : https://prove2.me/submissions/4d7a5c35-ef5f-4871-b161-ee4c9d7b7d30

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PermExpInj
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PowSum
import Theorems.Thm_Formalism_DegreeFormula_PPowSum_permExp_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.DegreeFormula Formalism.DegreeFormula.PPowSum
open Formalism.DegreeFormula
namespace Formalism.DegreeFormula.PPowSum
theorem _root_.solution {ι : Type} [Fintype ι] {N : ℕ} (σ : ι → Equiv.Perm (Fin N)) :
    (permExp σ).degree = dimFl ι N := by
  rw [Finsupp.degree_eq_sum]
  simp only [permExp_apply]
  rw [Fintype.sum_prod_type]
  have h : ∀ t : ι, ∑ i : Fin N, (N - 1 - ((σ t i : Fin N) : ℕ)) = N * (N - 1) / 2 := by
    intro t
    rw [Equiv.sum_comp (σ t) (fun j : Fin N => N - 1 - (j : ℕ)),
      Fin.sum_univ_eq_sum_range (fun j => N - 1 - j) N, Finset.sum_range_reflect (fun j => j) N,
      Finset.sum_range_id]
  simp only [h, Finset.sum_const, Finset.card_univ, smul_eq_mul, dimFl]
end Formalism.DegreeFormula.PPowSum
