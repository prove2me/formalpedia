-- Prove2me | solution 2 for BlockPoly.coeff_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:40.092134+00:00
-- url     : https://prove2.me/submissions/65c00410-80ed-48b6-9fb3-62bf5588dbc2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_MapDomainMemOfDvd
import Theorems.Thm_BlockPoly_diag_monomial

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
theorem _root_.solution (c : σ → K) (g : MvPolynomial σ K) (s : σ →₀ ℕ) :
    coeff s (diag c g) = (s.prod fun t e => c t ^ e) * coeff s g := by
  classical
  induction g using MvPolynomial.induction_on' with
  | monomial m a =>
    rw [diag_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; ring
    · simp
  | add p q hp hq =>
    rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]
end BlockPoly
