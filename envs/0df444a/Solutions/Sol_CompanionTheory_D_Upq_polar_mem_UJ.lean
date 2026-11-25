-- Prove2me | solution 1 for CompanionTheory.D.Upq.polar_mem_UJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:41:27.966424+00:00
-- url     : https://prove2.me/submissions/bb045fcb-7ce2-4941-8643-8e46896712d4

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_CoePolarExpHomeomorphComplexApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MaximalCompactIsCompact
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_PolarUH
import Theorems.Thm_CompanionTheory_D_Upq_mul_J_mul_conjTranspose
import Theorems.Thm_CompanionTheory_D_Upq_sqrt_mem_UJ
import Theorems.Thm_CompanionTheory_D_Upq_mul_mem_UJ
import Theorems.Thm_CompanionTheory_D_Upq_inv_mem_UJ

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
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
set_option linter.unusedSectionVars false
variable {m : Type*} [Fintype m] [DecidableEq m] {J : Matrix m m ℂ}
namespace CompanionTheory.D.Upq
theorem _root_.solution (hJJ : J * J = 1) (hJh : Jᴴ = J) (g : GL m ℂ)
    (hg : (g : Matrix m m ℂ)ᴴ * J * g = J) :
    (polarPos g)ᴴ * J * polarPos g = J ∧ (polarUnitary g)ᴴ * J * polarUnitary g = J := by
  have hp : (polarPos g)ᴴ * J * polarPos g = J := by
    refine sqrt_mem_UJ hJJ hJh (posDef_conjTranspose_mul_self_GL g) ?_
    have hg' := mul_J_mul_conjTranspose hJJ hg
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
    calc (g : Matrix m m ℂ)ᴴ * g * J * ((g : Matrix m m ℂ)ᴴ * g)
        = (g : Matrix m m ℂ)ᴴ * ((g : Matrix m m ℂ) * J * (g : Matrix m m ℂ)ᴴ) * g := by
          simp only [Matrix.mul_assoc]
      _ = J := by rw [hg', hg]
  exact ⟨hp, mul_mem_UJ hg (inv_mem_UJ (isUnit_det_of_posDef (polarPos_posDef g)) hp)⟩
end CompanionTheory.D.Upq
