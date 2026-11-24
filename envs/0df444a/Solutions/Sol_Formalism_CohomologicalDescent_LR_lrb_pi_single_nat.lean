-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrb_pi_single_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:51:36.836363+00:00
-- url     : https://prove2.me/submissions/db8d2549-0330-46a8-86a2-00ae75ae2503

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrbPiSingleCast
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LR
open Formalism.GradedWeylDivisibility
variable (R : Type*) [CommRing R] (p q : ℕ)
namespace Formalism.CohomologicalDescent.LR
theorem _root_.solution (c : Fin q) : lrbPi p q (Pi.single (Fin.natAdd p c) 1) = Pi.single c 1 := by
  funext t
  change (Pi.single (Fin.natAdd p c) 1 : Fin (p + q) → ℕ) (Fin.natAdd p t) = _
  by_cases h : t = c
  · subst h
    simp
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne (fun h' => h (by simpa using h'))]
end Formalism.CohomologicalDescent.LR
