-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.nablaLDiag_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:59.343526+00:00
-- url     : https://prove2.me/submissions/b2541d77-d5a2-4ff6-b287-4ad53d0f294f

import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_NablaLBasis
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_NablaLDiag
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldlat_isWH_map
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (h1 : RowActMul) (h2 : RowActDiagWeight) (h3 : NablaLBasis) : NablaLDiag := by
  intro R K _ _ _ _ hinj k n ν ι b μ hb g t hg ht
  have hD : IsUnit (Matrix.diagonal t).det := by
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => ht a)
  have hgD : IsUnit (g * Matrix.diagonal t).det := by
    rw [Matrix.det_mul]
    exact hg.mul hD
  have hDinv : (Matrix.diagonal t)⁻¹ = Matrix.diagonal (fun a => (t a)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    convert Matrix.diagonal_one with a
    exact inv_mul_cancel₀ (ht a)
  have hfam : (fun i => rowAct K (g * Matrix.diagonal t)⁻¹ (map (algebraMap R K) (b i))) =
      fun i => (∏ a, t a ^ μ i a)⁻¹ • rowAct K g⁻¹ (map (algebraMap R K) (b i)) := by
    funext i
    rw [Matrix.mul_inv_rev, ← h1 K k n g⁻¹ (Matrix.diagonal t)⁻¹, AlgHom.comp_apply, hDinv,
      h2 K k n _ (μ i) _ (ldlat_isWH_map _ (hb.2.2 i)), map_smul]
    congr 1
    rw [← Finset.prod_inv_distrib]
    simp [inv_pow]
  obtain ⟨hl, hs⟩ := h3 R K hinj k n ν b μ hb (g * Matrix.diagonal t) hgD
  rw [hfam] at hl hs
  exact ⟨hl, hs⟩
end Formalism.GradedWeylDivisibility
