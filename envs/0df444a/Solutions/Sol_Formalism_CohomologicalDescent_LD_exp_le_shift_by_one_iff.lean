-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.exp_le_shift_by_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:47:57.033839+00:00
-- url     : https://prove2.me/submissions/cda53fd7-70a0-4f5f-ab5e-3041be573f96

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_det_weighted_homog_ones
import Theorems.Thm_Formalism_CohomologicalDescent_LA_det_dvd_of_mem_dual_weyl_shift
import Theorems.Thm_Formalism_CohomologicalDescent_LA_det_mul_mem_dual_weyl_shift
import Theorems.Thm_Formalism_CohomologicalDescent_LA_generic_det_ne_zero
import Theorems.Thm_Formalism_CohomologicalDescent_LA_mem_dual_weyl_of_det_mul
import Theorems.Thm_Formalism_CohomologicalDescent_LA_weighted_homogeneous_cancel
import Theorems.Thm_Formalism_CohomologicalDescent_LA_weyl_shift_eq_map_det_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution (l r : ℕ) (ν μ : Fin r → ℕ) (e : ℕ) (hν : Antitone ν) :
    ExpLe l r (fun a => ν a + 1) (fun a => μ a + 1) e ↔ ExpLe l r ν μ e := by
  have e1 : (fun a => μ a + 1) = (fun _ : Fin r => 1) + μ := by
    funext a
    simp [add_comm]
  constructor
  · intro h x hx
    have hx' : genericDet ℤ r * x ∈ nablaWt r (fun a => ν a + 1) (fun a => μ a + 1) := by
      refine ⟨det_mul_mem_dual_weyl_shift ν hx.1, ?_⟩
      rw [e1]
      exact (det_weighted_homog_ones r).mul hx.2
    obtain ⟨m, hm, h1⟩ := h _ hx'
    refine ⟨m, hm, ?_⟩
    rw [weyl_shift_eq_map_det_mul] at h1
    obtain ⟨z, hz, hzz⟩ := h1
    simp only [LinearMap.mulLeft_apply] at hzz
    rw [← mul_smul_comm] at hzz
    rw [← mul_left_cancel₀ (generic_det_ne_zero r) hzz]
    exact hz
  · intro h x hx
    obtain ⟨y, rfl⟩ := det_dvd_of_mem_dual_weyl_shift ν hν hx.1
    have hy : y ∈ nablaWt r ν μ := by
      refine ⟨mem_dual_weyl_of_det_mul ν hx.1, ?_⟩
      have h2 := hx.2
      rw [e1] at h2
      exact weighted_homogeneous_cancel _ _ y (fun _ => 1) μ (generic_det_ne_zero r) (det_weighted_homog_ones r) h2
    obtain ⟨m, hm, h1⟩ := h y hy
    refine ⟨m, hm, ?_⟩
    rw [weyl_shift_eq_map_det_mul]
    refine ⟨_, h1, ?_⟩
    simp only [LinearMap.mulLeft_apply]
    rw [mul_smul_comm]
end Formalism.CohomologicalDescent.LD
