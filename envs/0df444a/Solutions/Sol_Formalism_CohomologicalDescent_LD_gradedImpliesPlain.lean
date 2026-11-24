-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.gradedImpliesPlain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:43:34.062982+00:00
-- url     : https://prove2.me/submissions/27944a49-a096-44a6-af06-f9878355a8e9

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
theorem _root_.solution : GradedImpliesPlain := by
  intro h l p q w lam2 hl ha hw eL heL i μ hd
  have h0 : Antitone (0 : Fin (p + q) → ℤ) := fun _ _ _ => le_rfl
  refine h l p q w lam2 0 hl ha hw h0 0 eL (fun μ2 _ => heL μ2) i μ hd ?_
  simp [depth2]
end Formalism.CohomologicalDescent.LD
