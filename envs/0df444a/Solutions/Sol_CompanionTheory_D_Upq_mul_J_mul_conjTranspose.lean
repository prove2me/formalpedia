-- Prove2me | solution 1 for CompanionTheory.D.Upq.mul_J_mul_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:54:33.809811+00:00
-- url     : https://prove2.me/submissions/7f7015eb-02aa-46f7-a1ce-48c3adf0f6cd

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_CoePolarExpHomeomorphComplexApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MaximalCompactIsCompact
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_PolarUH

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
theorem _root_.solution (hJJ : J * J = 1) {g : Matrix m m ℂ} (hg : gᴴ * J * g = J) :
    g * J * gᴴ = J := by
  have h1 : (J * gᴴ * J) * g = 1 := by
    calc (J * gᴴ * J) * g = J * (gᴴ * J * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, hJJ]
  have h2 : g * (J * gᴴ * J) = 1 := mul_eq_one_comm.1 h1
  calc g * J * gᴴ = g * (J * gᴴ * J) * J := by simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
    _ = J := by rw [h2, Matrix.one_mul]
end CompanionTheory.D.Upq
