-- Prove2me | solution 2 for BlockPoly.support_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:02.689697+00:00
-- url     : https://prove2.me/submissions/f35ad606-75f5-4453-9ac7-52a2bfcee672

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_MapDomainMemOfDvd
import Theorems.Thm_BlockPoly_coeff_diag

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
theorem _root_.solution {c : σ → K} (hc : ∀ t, c t ≠ 0) (g : MvPolynomial σ K) :
    (diag c g).support = g.support := by
  have hne : (s : σ →₀ ℕ) → (s.prod fun t e => c t ^ e) ≠ 0 := fun s =>
    Finset.prod_ne_zero_iff.mpr fun t _ => pow_ne_zero _ (hc t)
  ext s
  simp only [mem_support_iff, coeff_diag]
  exact ⟨fun h => right_ne_zero_of_mul h, fun h => mul_ne_zero (hne s) h⟩
end BlockPoly
