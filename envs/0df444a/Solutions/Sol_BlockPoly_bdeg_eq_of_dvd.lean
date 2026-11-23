-- Prove2me | solution 1 for BlockPoly.bdeg_eq_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:53.438192+00:00
-- url     : https://prove2.me/submissions/6368caaa-2027-4944-a8a8-321e57964bbe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_MapDomainMemOfDvd
import Theorems.Thm_BlockPoly_coeff_diag
import Theorems.Thm_BlockPoly_support_diag
import Theorems.Thm_BlockPoly_totalDegree_diag
import Theorems.Thm_BlockPoly_eq_mul_C_of_dvd
import Theorems.Thm_BlockPoly_cb_ne_zero
import Theorems.Thm_BlockPoly_prod_cb

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
theorem _root_.solution [CharZero K] (b : Fin (D + 1))
    {g : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K}
    (hd : g ∣ diag (cb b (2 : K)) g) {s s' : Fin (D + 1) × Fin (N + 1) →₀ ℕ}
    (hs : s ∈ g.support) (hs' : s' ∈ g.support) : bdeg b s = bdeg b s' := by
  have hg : g ≠ 0 := by
    rintro rfl
    simp at hs
  have h2 : ∀ t : Fin (D + 1) × Fin (N + 1), cb b (2 : K) t ≠ 0 := cb_ne_zero two_ne_zero b
  have hne : diag (cb b (2 : K)) g ≠ 0 := by
    intro h
    apply hg
    rw [← support_eq_empty, ← support_diag h2 g, h, support_zero]
  obtain ⟨a, ha⟩ := eq_mul_C_of_dvd hd (totalDegree_diag h2 g) hne
  have key : ∀ r ∈ g.support, (2 : K) ^ bdeg b r = a := by
    intro r hr
    have h3 := congrArg (coeff r) ha
    rw [coeff_diag, prod_cb, coeff_C_mul] at h3
    exact mul_right_cancel₀ (mem_support_iff.mp hr) h3
  have e := (key s hs).trans (key s' hs').symm
  have e' : ((2 ^ bdeg b s : ℕ) : K) = ((2 ^ bdeg b s' : ℕ) : K) := by
    push_cast
    exact e
  exact Nat.pow_right_injective (le_refl 2) (Nat.cast_injective e')
end BlockPoly
