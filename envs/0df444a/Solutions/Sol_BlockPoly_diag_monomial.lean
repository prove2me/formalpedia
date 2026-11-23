-- Prove2me | solution 1 for BlockPoly.diag_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:13.306091+00:00
-- url     : https://prove2.me/submissions/d04f6726-7528-47e9-9679-b1aeb759db56

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
variable {K σ : Type*} [Field K]
namespace BlockPoly
theorem _root_.solution (c : σ → K) (m : σ →₀ ℕ) (a : K) :
    diag c (monomial m a) = monomial m (a * m.prod fun t e => c t ^ e) := by
  unfold diag
  rw [aeval_monomial, algebraMap_eq, monomial_eq, C_mul, mul_assoc]
  congr 1
  simp only [mul_pow, Finsupp.prod, Finset.prod_mul_distrib, map_prod, map_pow]
end BlockPoly
