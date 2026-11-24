-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.ld_sym_nu_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:43:36.820869+00:00
-- url     : https://prove2.me/submissions/c84225f3-142d-4772-be87-f18522f2b7d8

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution (q w : ℕ) (s : Fin (1 + q)) (hs : s ≠ ldZ q) : blockWt 1 q w (fun _ => 0) s = 0 := by
  induction s using Fin.addCases with
  | left i =>
    exfalso
    apply hs
    simp only [ldZ]
    congr 1
    exact Subsingleton.elim _ _
  | right j => simp only [blockWt, Fin.append_right]
end Formalism.CohomologicalDescent.LD
