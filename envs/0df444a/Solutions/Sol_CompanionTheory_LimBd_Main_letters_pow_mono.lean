-- Prove2me | solution 1 for CompanionTheory.LimBd.Main.letters_pow_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:56:58.269624+00:00
-- url     : https://prove2.me/submissions/d19dbf3c-4b9c-44e4-94ef-acc9fc56fd2a

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_HeckeMultiplication
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_GeneratingFunctionPolynomial
import Theorems.Thm_CompanionTheory_LimBd_Main_letters_pow_succ

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
theorem _root_.solution {d e : ℕ} (hde : d ≤ e) {q : B.Mat k r → ℂ} (h : q ∈ Letters k r ^ d) :
    q ∈ Letters k r ^ e := by
  induction hde with
  | refl => exact h
  | step _ ih => exact letters_pow_succ ih
end CompanionTheory.LimBd.Main
