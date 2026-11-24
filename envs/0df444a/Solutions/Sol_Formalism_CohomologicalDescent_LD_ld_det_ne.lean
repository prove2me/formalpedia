-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.ld_det_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:43:34.794652+00:00
-- url     : https://prove2.me/submissions/4e5390fb-54d5-4053-9963-8af8f2df5d5d

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
theorem _root_.solution : ldDet ≠ 0 := by
  intro h
  have h' := congrArg (MvPolynomial.eval (fun v : Fin 2 × Fin 2 => if v.1 = v.2 then (1 : ℤ) else 0)) h
  simp [ldDet] at h'
end Formalism.CohomologicalDescent.LD
