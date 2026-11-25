-- Prove2me | solution 1 for CompanionTheory.D.Upq.existsUnique_complexification
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:08:48.688249+00:00
-- url     : https://prove2.me/submissions/072dec08-a1bf-4a5d-948d-06ad7f4cbcc0

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ContDiffOnExpPartialHomeomorphSymm
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ExistsUniqueComplexification
import Theorems.Thm_CompanionTheory_D_Upq_reG_mem
import Theorems.Thm_CompanionTheory_D_Upq_imG_mem
import Theorems.Thm_CompanionTheory_D_Upq_reG_add_I_smul_imG
import Theorems.Thm_CompanionTheory_D_Upq_eq_reG_imG_of_eq

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
theorem _root_.solution (M : Matrix n n ℂ) :
    ∃! XY : Matrix n n ℂ × Matrix n n ℂ, XY.1 ∈ lieJ J ∧ XY.2 ∈ lieJ J ∧ M = XY.1 + Complex.I • XY.2 :=
  ⟨(reG J M, imG J M), ⟨reG_mem hJ hJh M, imG_mem hJ hJh M, reG_add_I_smul_imG M⟩,
    fun XY h => by
      obtain ⟨h1, h2⟩ := eq_reG_imG_of_eq hJ hJh h.1 h.2.1 h.2.2
      exact Prod.ext h1 h2⟩
end CompanionTheory.D.Upq
