-- Prove2me | solution 1 for BlockPoly.translEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:57.453904+00:00
-- url     : https://prove2.me/submissions/a2e21e40-7a50-492c-8ed6-5c7462e58b4f

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
theorem _root_.solution (a : Fin (N + 1) → K)
    (g : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K) : translEquiv a g = transl a g := rfl
end BlockPoly
