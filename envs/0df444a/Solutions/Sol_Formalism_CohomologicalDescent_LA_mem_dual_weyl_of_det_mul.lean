-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.mem_dual_weyl_of_det_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:13:34.451799+00:00
-- url     : https://prove2.me/submissions/8d8d1640-c2ac-4f3f-9f83-56b240353f81

import Definitions.Def_Formalism_PieriBlockIdeals_ExZTranslate
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Theorems.Thm_Formalism_CohomologicalDescent_LA_generic_det_ne_zero
import Theorems.Thm_Formalism_CohomologicalDescent_LA_det_mem_dual_weyl_ones
import Theorems.Thm_Formalism_CohomologicalDescent_LA_weighted_homogeneous_cancel
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution {r : ℕ} (ν : Fin r → ℕ) {g : MvPolynomial (Fin r × Fin r) ℤ}
    (h : genericDet ℤ r * g ∈ dualWeyl ℤ r r (fun a => ν a + 1)) : g ∈ dualWeyl ℤ r r ν := by
  have hd := det_mem_dual_weyl_ones r
  have hne : rename (R := ℤ) (some : Fin r × Fin r → Option (Fin r × Fin r)) (genericDet ℤ r) ≠ 0 := by
    intro h0
    apply generic_det_ne_zero r
    apply MvPolynomial.rename_injective _ (Option.some_injective _)
    rw [h0, map_zero]
  unfold dualWeyl at h hd ⊢
  rw [Submodule.mem_inf] at h hd ⊢
  obtain ⟨h1, h2⟩ := h
  obtain ⟨hd1, hd2⟩ := hd
  constructor
  · rw [mem_weightedHomogeneousSubmodule] at h1 hd1 ⊢
    have e : (fun a => ν a + 1) = (fun _ => 1) + ν := by
      funext a
      simp only [Pi.add_apply]
      omega
    rw [e] at h1
    exact weighted_homogeneous_cancel (colW r r) (genericDet ℤ r) g (fun _ => 1) ν (generic_det_ne_zero r) hd1 h1
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      AlgHom.toLinearMap_apply, sub_eq_zero] at h2 hd2 ⊢
    intro l j hlj
    have h3 := h2 l j hlj
    rw [map_mul, map_mul, hd2 l j hlj] at h3
    exact mul_left_cancel₀ hne h3
end Formalism.CohomologicalDescent.LA
