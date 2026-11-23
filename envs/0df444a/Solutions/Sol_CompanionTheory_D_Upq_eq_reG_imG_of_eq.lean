-- Prove2me | solution 1 for CompanionTheory.D.Upq.eq_reG_imG_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:06.728573+00:00
-- url     : https://prove2.me/submissions/840e7d58-7c28-42cf-9cab-7188f1962da8

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ContDiffOnExpPartialHomeomorphSymm
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ExistsUniqueComplexification
import Theorems.Thm_CompanionTheory_D_Upq_thetaG_add
import Theorems.Thm_CompanionTheory_D_Upq_thetaG_smul
import Theorems.Thm_CompanionTheory_D_Upq_mem_lieJ_iff_thetaG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq
open Matrix
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (J : Matrix n n ℂ)
variable {J}
variable (hJ : J * J = 1) (hJh : Jᴴ = J)
include hJ hJh
namespace CompanionTheory.D.Upq
theorem _root_.solution {M X Y : Matrix n n ℂ} (hX : X ∈ lieJ J) (hY : Y ∈ lieJ J)
    (hM : M = X + Complex.I • Y) : X = reG J M ∧ Y = imG J M := by
  have hM' : thetaG J M = X - Complex.I • Y := by
    rw [hM, thetaG_add, thetaG_smul, (mem_lieJ_iff_thetaG hJ).1 hX,
      (mem_lieJ_iff_thetaG hJ).1 hY, Complex.star_def, Complex.conj_I, neg_smul, ← sub_eq_add_neg]
  refine ⟨?_, ?_⟩
  · rw [reG, hM', hM, add_add_sub_cancel, ← two_smul ℂ X, smul_smul]
    norm_num
  · rw [imG, hM', hM, add_sub_sub_cancel, ← two_smul ℂ, smul_smul, smul_smul,
      show -(Complex.I / 2) * 2 * Complex.I = 1 by
        rw [neg_mul, neg_mul, div_mul_cancel₀ _ two_ne_zero, Complex.I_mul_I, neg_neg], one_smul]
end CompanionTheory.D.Upq
