-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_xy_mem_binLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:27:21.307109+00:00
-- url     : https://prove2.me/submissions/290ce9e4-3b2e-42f0-83e2-369dd433fa75

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution (R : Type) [CommRing R] {n : ℕ} (s : Fin n) (d : ℕ) :
    la_xy R s d 0 ∈ la_binLat R s d := by
  rw [la_binLat]
  exact Submodule.subset_span ⟨d, 0, by simp, by simp⟩
end Formalism.CohomologicalDescent.LA
