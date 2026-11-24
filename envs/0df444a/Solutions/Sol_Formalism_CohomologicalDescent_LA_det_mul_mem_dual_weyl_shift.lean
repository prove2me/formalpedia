-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.det_mul_mem_dual_weyl_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:13:33.030822+00:00
-- url     : https://prove2.me/submissions/f3be577d-4c5c-4e0e-a4f1-cf3ccf574ea3

import Definitions.Def_Formalism_PieriBlockIdeals_ExZTranslate
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Theorems.Thm_Formalism_CohomologicalDescent_LA_det_mem_dual_weyl_ones
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
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution {r : ℕ} (ν : Fin r → ℕ) {g : MvPolynomial (Fin r × Fin r) ℤ}
    (hg : g ∈ dualWeyl ℤ r r ν) : genericDet ℤ r * g ∈ dualWeyl ℤ r r (fun a => ν a + 1) := by
  have hd := det_mem_dual_weyl_ones r
  unfold dualWeyl at hg hd ⊢
  rw [Submodule.mem_inf] at hg hd ⊢
  obtain ⟨hg1, hg2⟩ := hg
  obtain ⟨hd1, hd2⟩ := hd
  constructor
  · rw [mem_weightedHomogeneousSubmodule] at hg1 hd1 ⊢
    have h := hd1.mul hg1
    convert h using 1
    funext a
    simp only [Pi.add_apply]
    omega
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      AlgHom.toLinearMap_apply, sub_eq_zero] at hg2 hd2 ⊢
    intro l j hlj
    rw [map_mul, map_mul, hd2 l j hlj, hg2 l j hlj]
end Formalism.CohomologicalDescent.LA
