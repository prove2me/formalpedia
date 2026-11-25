-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.incl_z_shift_by_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:47:57.947424+00:00
-- url     : https://prove2.me/submissions/ae208fc8-c8be-403a-b22e-a5ad86064fed

import Definitions.Def_Formalism_PieriBlockIdeals_ExZTranslate
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Theorems.Thm_Formalism_CohomologicalDescent_LA_weyl_shift_eq_map_det_mul
import Theorems.Thm_Formalism_CohomologicalDescent_LA_generic_det_ne_zero
import Theorems.Thm_Formalism_CohomologicalDescent_LA_det_mul_mem_dual_weyl_shift
import Theorems.Thm_Formalism_CohomologicalDescent_LA_mem_dual_weyl_of_det_mul
import Theorems.Thm_Formalism_CohomologicalDescent_LA_det_dvd_of_mem_dual_weyl_shift
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
theorem _root_.solution (r : ℕ) (ν : Fin r → ℕ) (l e : ℕ) (hν : Antitone ν) :
    InclZ r r le_rfl (fun a => ν a + 1) l e ↔ InclZ r r le_rfl ν l e := by
  unfold InclZ
  have hW := weyl_shift_eq_map_det_mul ℤ ν
  have hdn := generic_det_ne_zero r
  constructor
  · rintro ⟨m, hm, h⟩
    refine ⟨m, hm, fun x hx => ?_⟩
    have h1 := h _ (det_mul_mem_dual_weyl_shift ν hx)
    rw [hW] at h1
    obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.mp h1
    rw [LinearMap.mulLeft_apply] at hxy
    have hyx : y = ((m * l ^ e : ℕ) : ℤ) • x := by
      apply mul_left_cancel₀ hdn
      rw [hxy, mul_smul_comm]
    rw [← hyx]
    exact hy
  · rintro ⟨m, hm, h⟩
    refine ⟨m, hm, fun x hx => ?_⟩
    obtain ⟨g, rfl⟩ := det_dvd_of_mem_dual_weyl_shift ν hν hx
    have hg := mem_dual_weyl_of_det_mul ν hx
    rw [hW, ← mul_smul_comm]
    exact Submodule.mem_map.mpr ⟨_, h g hg, by simp⟩
end Formalism.CohomologicalDescent.LA
