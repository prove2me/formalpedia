-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lcplead_hom_row
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:13:19.851799+00:00
-- url     : https://prove2.me/submissions/8dfb9773-91ae-4241-9cee-36fa67d68c5f

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCpleadLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lcplead_weight_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open scoped MonomialOrder
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
variable {B : Type*} [CommRing B] {r n : ℕ} {l j : Fin n}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (hlj : l ≠ j) {ω : Fin r × Fin n →₀ ℕ} {g : MvPolynomial (Fin r × Fin n) B}
    (hg : IsWeightedHomogeneous (pairW l j) g ω) {m : Fin r × Fin n →₀ ℕ} (hm : m ∈ g.support)
    (b : Fin r) : m (b, l) + m (b, j) = ω (b, l) := by
  rw [← hg (mem_support_iff.mp hm), lcplead_weight_apply l j hlj m b l, if_pos rfl]
end Formalism.GradedWeylDivisibility
