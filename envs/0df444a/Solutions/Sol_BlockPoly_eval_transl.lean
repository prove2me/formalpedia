-- Prove2me | solution 1 for BlockPoly.eval_transl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:53.145784+00:00
-- url     : https://prove2.me/submissions/3d3e6654-1957-4b6f-9f3c-83714b0e1bea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_MapDomainMemOfDvd
import Theorems.Thm_BlockPoly_translEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply

set_option autoImplicit false
open BlockPoly
open MvPolynomial
variable {K : Type*} [Field K] {D N : ℕ}
namespace BlockPoly
theorem _root_.solution (z : Fin (D + 1) × Fin (N + 1) → K)
    (f : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K) :
    eval (fun t => if t.1 = 0 then 0 else z t) (transl (fun j => z (0, j)) f) = eval z f := by
  induction f using MvPolynomial.induction_on
  next c =>
    simp only [algHom_C, eval_C, AlgHom.commutes, algebraMap_eq]
  next p q hp hq =>
    simp only [map_add, hp, hq]
  next p t hp =>
    obtain ⟨i, j⟩ := t
    simp only [map_mul, hp, transl_X]
    congr 1
    by_cases h : i = 0
    · subst h
      simp
    · simp [h]
end BlockPoly
