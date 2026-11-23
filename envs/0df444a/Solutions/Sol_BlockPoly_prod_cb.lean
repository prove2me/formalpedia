-- Prove2me | solution 1 for BlockPoly.prod_cb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:31.426426+00:00
-- url     : https://prove2.me/submissions/683e3636-175e-4575-917c-feb665cdde3f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_MapDomainMemOfDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open BlockPoly
open MvPolynomial
variable {K : Type*} [Field K] {D N : ℕ}
namespace BlockPoly
theorem _root_.solution (b : Fin (D + 1)) (μ : K) (s : Fin (D + 1) × Fin (N + 1) →₀ ℕ) :
    (s.prod fun t e => cb b μ t ^ e) = μ ^ bdeg b s := by
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type,
    Fintype.prod_eq_single b]
  · simp [cb, bdeg, Finset.prod_pow_eq_pow_sum]
  · intro i hi
    simp [cb, hi]
end BlockPoly
