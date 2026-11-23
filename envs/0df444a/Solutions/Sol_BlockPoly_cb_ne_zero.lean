-- Prove2me | solution 1 for BlockPoly.cb_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:57.593808+00:00
-- url     : https://prove2.me/submissions/d0907a3a-e90a-4225-b68a-d691c0e706fb

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
theorem _root_.solution {μ : K} (hμ : μ ≠ 0) (b : Fin (D + 1)) (t : Fin (D + 1) × Fin (N + 1)) :
    cb b μ t ≠ 0 := by
  unfold cb
  split_ifs
  · exact hμ
  · exact one_ne_zero
end BlockPoly
