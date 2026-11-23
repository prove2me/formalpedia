-- Prove2me | solution 1 for BlockPoly.mapDomain_mem_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:13.528841+00:00
-- url     : https://prove2.me/submissions/ae1f8b9e-0282-424d-b3bd-fee2d72b0b6d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_MapDomainMemOfDvd
import Theorems.Thm_BlockPoly_eq_mul_C_of_dvd

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
theorem _root_.solution (e : Equiv.Perm (Fin (D + 1)))
    {g : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K}
    (hd : g ∣ rename (eT e) g) {s : Fin (D + 1) × Fin (N + 1) →₀ ℕ} (hs : s ∈ g.support) :
    s.mapDomain (eT e) ∈ g.support := by
  have hinj : Function.Injective (eT (N := N) e) := (eT (N := N) e).injective
  have hg : g ≠ 0 := by
    rintro rfl
    simp at hs
  have hr : rename (eT e) g ≠ 0 :=
    (map_ne_zero_iff _ (rename_injective _ hinj)).mpr hg
  have hdeg : (rename (eT e) g).totalDegree = g.totalDegree := by
    refine le_antisymm (totalDegree_rename_le _ g) ?_
    obtain ⟨q, hq⟩ := hd
    have hq0 : q ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hq
      exact hr hq
    rw [hq, totalDegree_mul_of_isDomain hg hq0]
    omega
  obtain ⟨a, ha⟩ := eq_mul_C_of_dvd hd hdeg hr
  have h1 := congrArg (coeff (s.mapDomain (eT e))) ha
  rw [coeff_rename_mapDomain _ hinj, coeff_C_mul] at h1
  rw [mem_support_iff] at hs ⊢
  intro h0
  rw [h0, mul_zero] at h1
  exact hs h1
end BlockPoly
