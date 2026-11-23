-- Prove2me | solution 1 for BlockPoly.eq_zero_of_transl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:43.481862+00:00
-- url     : https://prove2.me/submissions/ccebb011-1607-4b51-b7df-abac807b40ce

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_MapDomainMemOfDvd
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_BlockPoly_eval_transl
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
theorem _root_.solution [Infinite K] {g : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K}
    (hd : ∀ a, g ∣ transl a g) (h0 : ∀ s ∈ g.support, 0 < bdeg 0 s) : g = 0 := by
  have hz : ∀ z : Fin (D + 1) × Fin (N + 1) → K,
      eval (fun t => if t.1 = 0 then 0 else z t) g = 0 := by
    intro z
    rw [eval_eq']
    refine Finset.sum_eq_zero fun s hs => ?_
    obtain ⟨j, hj⟩ : ∃ j, s (0, j) ≠ 0 := by
      by_contra hne
      push_neg at hne
      have h1 := h0 s hs
      simp [bdeg, hne] at h1
    apply mul_eq_zero_of_right
    exact Finset.prod_eq_zero (Finset.mem_univ (0, j)) (by simp [hj])
  apply MvPolynomial.funext
  intro z
  obtain ⟨q, hq⟩ := hd (fun j => z (0, j))
  rw [map_zero, ← eval_transl z g, hq, map_mul, hz, zero_mul]
end BlockPoly
