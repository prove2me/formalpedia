-- Prove2me | solution 1 for CompanionTheory.LimBd.Main.letters_pow_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:59:32.010123+00:00
-- url     : https://prove2.me/submissions/b22e8425-6e7c-4c75-a926-3df7d6a7d087

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_HeckeMultiplication
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_GeneratingFunctionPolynomial
import Theorems.Thm_CompanionTheory_LimBd_Main_one_mem_letters

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.Main
open Formalism.FourierDecayAlt PI.UpqRep Matrix
open scoped ComplexConjugate
variable {k r : ℕ}
namespace CompanionTheory.LimBd.Main
theorem _root_.solution {d : ℕ} {q : B.Mat k r → ℂ} (h : q ∈ Letters k r ^ d) : q ∈ Letters k r ^ (d + 1) := by
  rw [pow_succ]
  simpa using Submodule.mul_mem_mul h one_mem_letters
end CompanionTheory.LimBd.Main
