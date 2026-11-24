-- Prove2me | solution 1 for Formalism.IncomingBounds.Cay.der_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:03.854607+00:00
-- url     : https://prove2.me/submissions/751b9807-8a9c-411f-bab6-e85ce4d3641c

import Definitions.Def_Formalism_IncomingBounds_StatementThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds Formalism.IncomingBounds.Cay
open MvPolynomial Matrix
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (D : Derivation R A A)
namespace Formalism.IncomingBounds.Cay
theorem _root_.solution {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → A) :
    D (∏ j ∈ s, g j) = ∑ i ∈ s, D (g i) * ∏ j ∈ s.erase i, g j := by
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha, Finset.erase_insert ha,
    smul_eq_mul, smul_eq_mul, Finset.mul_sum]
  have key : ∀ i ∈ s, D (g i) * ∏ j ∈ (insert a s).erase i, g j =
      g a * (D (g i) * ∏ j ∈ s.erase i, g j) := by
    intro i hi
    have hne : a ≠ i := fun h => ha (h ▸ hi)
    rw [Finset.erase_insert_of_ne hne,
      Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
    ring
  rw [Finset.sum_congr rfl key]
  ring
end Formalism.IncomingBounds.Cay
