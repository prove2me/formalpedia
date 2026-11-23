-- Prove2me | solution 1 for BlockPoly.eq_mul_C_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:57.633977+00:00
-- url     : https://prove2.me/submissions/4f4ea7f4-5722-4983-9aec-04b59f6dd64b

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
theorem _root_.solution {g h : MvPolynomial σ K} (hd : g ∣ h)
    (hdeg : h.totalDegree = g.totalDegree) (hh : h ≠ 0) : ∃ a : K, h = C a * g := by
  obtain ⟨q, rfl⟩ := hd
  have hg : g ≠ 0 := left_ne_zero_of_mul hh
  have hq : q ≠ 0 := right_ne_zero_of_mul hh
  rw [totalDegree_mul_of_isDomain hg hq] at hdeg
  have hq0 : q.totalDegree = 0 := by omega
  refine ⟨q.coeff 0, ?_⟩
  rw [mul_comm]
  congr 1
  exact totalDegree_eq_zero_iff_eq_C.mp hq0
end BlockPoly
