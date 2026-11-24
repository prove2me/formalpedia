-- Prove2me | solution 1 for Formalism.IncomingBounds.Cay.der_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:30.818869+00:00
-- url     : https://prove2.me/submissions/0ae3282c-9f9d-4949-b4da-6323945672bc

import Definitions.Def_Formalism_IncomingBounds_StatementThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley
import Theorems.Thm_Formalism_IncomingBounds_Cay_der_prod

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
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] (N : Matrix n n A) :
    D N.det = ∑ i, ∑ p, adjugate N i p * D (N p i) := by
  have hcol : ∀ i, ∑ p, adjugate N i p * D (N p i) = (N.updateCol i fun p => D (N p i)).det := by
    intro i
    rw [← cramer_apply, cramer_eq_adjugate_mulVec]
    rfl
  rw [Finset.sum_congr rfl fun i _ => hcol i]
  simp only [det_apply']
  rw [map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Derivation.leibniz, Derivation.map_intCast, smul_zero, add_zero, smul_eq_mul,
    der_prod, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun x hx => ?_
    simp [Finset.ne_of_mem_erase hx]
end Formalism.IncomingBounds.Cay
