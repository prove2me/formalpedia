-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.le_locSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:20:16.726493+00:00
-- url     : https://prove2.me/submissions/8f55df87-da1e-4f97-86d0-09b3a52d530a

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrcFockZeroRight
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
namespace Formalism.CohomologicalDescent.LR
theorem _root_.solution (l : ℕ) (hl : l.Prime) {V : Type*} [AddCommGroup V] [Module ℚ V] (M : AddSubgroup V) {v : V}
    (hv : v ∈ M) : v ∈ locSpan l hl M :=
  ⟨1, fun h => by
    have := Int.natCast_dvd_natCast.1 (by simpa using h : ((l : ℕ) : ℤ) ∣ ((1 : ℕ) : ℤ))
    exact hl.one_lt.ne' (Nat.dvd_one.1 this), by simpa using hv⟩
end Formalism.CohomologicalDescent.LR
