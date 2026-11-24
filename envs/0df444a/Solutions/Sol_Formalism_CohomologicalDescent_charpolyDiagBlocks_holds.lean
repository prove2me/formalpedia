-- Prove2me | solution 1 for Formalism.CohomologicalDescent.charpolyDiagBlocks_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:41:31.366188+00:00
-- url     : https://prove2.me/submissions/8abf7626-2783-4806-99e5-76981604f822

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_StatementLW
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_MinorValuationBoundHolds
import Theorems.Thm_Formalism_CohomologicalDescent_lw_det_block

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open Formalism Formalism.CohomologicalDescent
namespace Formalism.CohomologicalDescent
theorem _root_.solution : CharpolyBlocks := by
  intro K _ n M b S r hM hS hchar
  have hC : (Matrix.charmatrix M).BlockTriangular b := by
    intro i j hij
    have hne : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hij
    simp [hne, hM hij]
  have hdet : M.charpoly
      = ∏ a ∈ univ.image b, ((Matrix.charmatrix M).toSquareBlock b a).det :=
    Matrix.BlockTriangular.det hC
  have hdvd : ∏ s ∈ S, (X - C (M s s)) ∣ M.charpoly := by
    rw [hdet]
    have h1 : ∏ s ∈ S, (X - C (M s s))
        = ∏ a ∈ S.image b, ((Matrix.charmatrix M).toSquareBlock b a).det := by
      rw [Finset.prod_image]
      · refine Finset.prod_congr rfl (fun s hs => ?_)
        rw [lw_det_block _ b s (hS s hs), Matrix.charmatrix_apply_eq]
      · intro x hx y _ hxy
        exact (hS x hx y hxy.symm).symm
    rw [h1]
    exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.image_subset_image (Finset.subset_univ S))
  have hne : M.charpoly ≠ 0 := (Matrix.charpoly_monic M).ne_zero
  have hroots := Polynomial.roots.le_of_dvd hne hdvd
  have e1 : ∏ s ∈ S, (X - C (M s s))
      = (Multiset.map (fun a => X - C a) (S.val.map (fun s => M s s))).prod := by
    rw [Multiset.map_map]
    rfl
  have e2 : ∏ u, (X - C (r u))
      = (Multiset.map (fun a => X - C a) ((Finset.univ : Finset (Fin n)).val.map r)).prod := by
    rw [Multiset.map_map]
    rfl
  rw [e1, Polynomial.roots_multiset_prod_X_sub_C, hchar, e2,
    Polynomial.roots_multiset_prod_X_sub_C] at hroots
  exact hroots
end Formalism.CohomologicalDescent
