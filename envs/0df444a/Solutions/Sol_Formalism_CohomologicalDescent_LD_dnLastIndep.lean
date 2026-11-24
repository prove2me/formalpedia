-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.dnLastIndep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:36:10.913308+00:00
-- url     : https://prove2.me/submissions/2ee93054-2719-408e-83b9-7656d057cfa4

import Definitions.Def_Formalism_PieriBlockIdeals_BranchingBoundLastGradedOneRow
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Theorems.Thm_Formalism_CohomologicalDescent_LD_dnShift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution : DnLastIndep := by
  intro p w i q M M' lam2 hwM hb hMM
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hMM
  have e1 : M + c - w = (M - w) + c := by omega
  have e2 : (fun b : Fin q => M + c - lam2 (Fin.rev b)) = fun b => (M - lam2 (Fin.rev b)) + c :=
    funext fun b => by
      have := hb (Fin.rev b)
      omega
  rw [e1, e2]
  exact dnShift p (M - w) i q c (fun b => M - lam2 (Fin.rev b)) fun b => by
    have := hb (Fin.rev b)
    omega
end Formalism.CohomologicalDescent.LD
