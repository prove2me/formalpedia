-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.nd_weight_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:16.354934+00:00
-- url     : https://prove2.me/submissions/a8b206d1-7466-4587-8261-521c62e44925

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LNondomLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
set_option linter.unusedSimpArgs false
variable {R : Type*} [CommRing R] {r n : ℕ}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (s : Fin n) (m : Fin r × Fin n →₀ ℕ) :
    Finsupp.weight (fun v => colW r n v s) m = Finsupp.weight (colW r n) m s := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply]
end Formalism.GradedWeylDivisibility
