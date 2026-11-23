-- Prove2me | solution 1 for BlockPoly.multiHom_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:39.101552+00:00
-- url     : https://prove2.me/submissions/bb25ee9d-ea4d-497c-8e3e-4c96c9eefae9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_MapDomainMemOfDvd
import Theorems.Thm_BlockPoly_bdeg_eq_of_dvd
import Theorems.Thm_BlockPoly_bdeg_mapDomain
import Theorems.Thm_BlockPoly_mapDomain_mem_of_dvd
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_BlockPoly_eq_zero_of_transl
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
theorem _root_.solution [CharZero K] {g : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K}
    (hsc : ∀ b, g ∣ diag (cb b (2 : K)) g)
    (hsw : ∀ e : Equiv.Perm (Fin (D + 1)), e 0 = 0 → g ∣ rename (eT e) g)
    (htr : ∀ a, g ∣ transl a g) (s : Fin (D + 1) × Fin (N + 1) →₀ ℕ) (hs : s ∈ g.support)
    (b : Fin (D + 1)) :
    ∑ j, s (b, j) = if b = 0 then 0 else g.support.sup fun r => ∑ j, r (1, j) := by
  have hc1 : ∀ b, ∀ r ∈ g.support, bdeg b r = bdeg b s := fun b r hr =>
    bdeg_eq_of_dvd b (hsc b) hr hs
  split_ifs with hb
  · subst hb
    show bdeg 0 s = 0
    by_contra hne
    haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
    have hg : g = 0 := eq_zero_of_transl htr fun r hr => by
      rw [hc1 0 r hr]
      exact Nat.pos_of_ne_zero hne
    rw [hg] at hs
    simp at hs
  · have hD : (1 : Fin (D + 1)) ≠ 0 := by
      intro h
      apply hb
      rcases D with _ | D
      · exact Fin.ext (Nat.lt_one_iff.mp b.isLt)
      · simp [Fin.ext_iff] at h
    have hb1 : bdeg b s = bdeg 1 s := by
      by_cases h1 : b = 1
      · rw [h1]
      · have he0 : Equiv.swap (1 : Fin (D + 1)) b 0 = 0 :=
          Equiv.swap_apply_of_ne_of_ne hD.symm (Ne.symm hb)
        have hmem := mapDomain_mem_of_dvd (Equiv.swap 1 b) (hsw _ he0) hs
        have h2 := bdeg_mapDomain (Equiv.swap (1 : Fin (D + 1)) b) 1 s
        rw [Equiv.swap_apply_left] at h2
        rw [← hc1 b _ hmem]
        exact h2
    show bdeg b s = g.support.sup fun r => bdeg 1 r
    rw [hb1]
    apply le_antisymm
    · exact Finset.le_sup (f := fun r => bdeg 1 r) hs
    · exact Finset.sup_le fun r hr => (hc1 1 r hr).le
end BlockPoly
