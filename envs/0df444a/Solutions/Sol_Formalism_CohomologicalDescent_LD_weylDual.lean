-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.weylDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:59:47.814228+00:00
-- url     : https://prove2.me/submissions/8affb789-3d16-4a04-92ff-7db4f94ebeed

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_gen_det_eq_det
import Theorems.Thm_Formalism_CohomologicalDescent_LD_weyl_le_of_stable_submodule
import Theorems.Thm_Formalism_CohomologicalDescent_LD_divided_power_cofactor
import Theorems.Thm_Formalism_CohomologicalDescent_LD_divided_power_det_pow_mul
import Theorems.Thm_Formalism_CohomologicalDescent_LD_highest_weight_dual_cofactor
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_hw_mem
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_weylRowDivStable
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
theorem _root_.solution : WeylDual := by
  intro r M ν hν hM
  rw [gen_det_eq_det]
  let L : Submodule ℤ (MvPolynomial (Fin r × Fin r) ℤ) :=
    ((weyl ℤ r r le_rfl (dualWt M ν)).map (LinearMap.mulLeft ℤ (genericDet ℤ r ^ (∑ a, ν a)))).comap
      ((LinearMap.mulLeft ℤ (genericDet ℤ r ^ M)).comp (cofMap r).toLinearMap)
  have hL : ∀ x, x ∈ L ↔ ∃ g ∈ weyl ℤ r r le_rfl (dualWt M ν),
      genericDet ℤ r ^ (∑ a, ν a) * g = genericDet ℤ r ^ M * cofMap r x := fun x => Iff.rfl
  have hle : weyl ℤ r r le_rfl ν ≤ L := by
    refine weyl_le_of_stable_submodule ν hν L ((hL _).2 ⟨_, la_hw_mem ℤ le_rfl _, highest_weight_dual_cofactor M ν hν hM⟩)
      fun a b hab k f hf => ?_
    obtain ⟨g, hg, hrel⟩ := (hL f).1 hf
    have hab' : Fin.rev b ≠ Fin.rev a := fun h => hab (Fin.rev_injective h).symm
    refine (hL _).2 ⟨((-1 : ℤ) ^ k) • rowDiv ℤ (Fin.rev b) (Fin.rev a) k g,
      Submodule.smul_mem _ _ (weylRowDivStable ℤ r r le_rfl _ _ _ k g hg), ?_⟩
    have h1 := divided_power_cofactor (Fin.rev b) (Fin.rev a) hab' k f
    rw [Fin.rev_rev, Fin.rev_rev] at h1
    rw [mul_smul_comm, ← divided_power_det_pow_mul _ _ hab', hrel, divided_power_det_pow_mul _ _ hab', h1, smul_eq_C_mul]
    have hsq : ((-1 : MvPolynomial (Fin r × Fin r) ℤ)) ^ k * (-1) ^ k = 1 := by
      rw [← mul_pow]
      simp
    have hC : (C ((-1 : ℤ) ^ k) : MvPolynomial (Fin r × Fin r) ℤ) = (-1) ^ k := by simp
    rw [hC]
    linear_combination (genericDet ℤ r ^ M * cofMap r (rowDiv ℤ a b k f)) * hsq
  exact fun x hx => (hL x).1 (hle hx)
end Formalism.CohomologicalDescent.LD
