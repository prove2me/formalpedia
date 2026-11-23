-- Prove2me | solution 1 for BlockPoly.bdeg_mapDomain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:13.173336+00:00
-- url     : https://prove2.me/submissions/25e972ac-eb78-42d7-92f3-a8e793dfa452

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
theorem _root_.solution (e : Equiv.Perm (Fin (D + 1))) (b : Fin (D + 1))
    (s : Fin (D + 1) × Fin (N + 1) →₀ ℕ) :
    bdeg (e b) (s.mapDomain (eT e)) = bdeg b s := by
  unfold bdeg
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : ((e b, j) : Fin (D + 1) × Fin (N + 1)) = eT e (b, j) := rfl
  rw [h, Finsupp.mapDomain_apply (eT e).injective]
end BlockPoly
