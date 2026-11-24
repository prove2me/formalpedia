-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.rev_cast_castAdd_eq_natAdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:17:28.136832+00:00
-- url     : https://prove2.me/submissions/4384627e-f0a8-4029-8dd7-95b8776dea3e

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
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
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution (p q : ℕ) (a : Fin p) :
    Fin.rev (Fin.cast (Nat.add_comm p q) (Fin.castAdd q a)) = Fin.natAdd q (Fin.rev a) := by
  apply Fin.ext
  have := a.isLt
  simp only [Fin.val_rev, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]
  omega
end Formalism.CohomologicalDescent.LD
