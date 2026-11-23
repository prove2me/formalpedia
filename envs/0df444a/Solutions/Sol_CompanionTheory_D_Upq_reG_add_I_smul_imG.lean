-- Prove2me | solution 1 for CompanionTheory.D.Upq.reG_add_I_smul_imG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:13.424716+00:00
-- url     : https://prove2.me/submissions/d14fe680-bf8e-4a44-99cf-e6f972a9ceaf

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ContDiffOnExpPartialHomeomorphSymm
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ExistsUniqueComplexification

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
omit hJ hJh
namespace CompanionTheory.D.Upq
theorem _root_.solution (M : Matrix n n ℂ) : M = reG J M + Complex.I • imG J M := by
  rw [reG, imG, smul_smul, show Complex.I * -(Complex.I / 2) = 1 / 2 by
    rw [mul_neg, ← mul_div_assoc, Complex.I_mul_I, neg_div, neg_neg], ← smul_add,
    add_add_sub_cancel, ← two_smul ℂ M, smul_smul]
  norm_num
end CompanionTheory.D.Upq
