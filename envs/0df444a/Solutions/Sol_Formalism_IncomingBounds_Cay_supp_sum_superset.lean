-- Prove2me | solution 1 for Formalism.IncomingBounds.Cay.supp_sum_superset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:15.798152+00:00
-- url     : https://prove2.me/submissions/2f2eac44-8712-49d6-a825-2ae4f3c12688

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
open MvPolynomial Matrix Formalism.IncomingBounds
variable {K : Type} [Field K] [CharZero K]
variable {σ M : Type} [AddCommMonoid M] (f : (σ →₀ ℕ) → K → M)
namespace Formalism.IncomingBounds.Cay
theorem _root_.solution (h0 : ∀ a, f a 0 = 0) (p : MvPolynomial σ K) (S : Finset (σ →₀ ℕ))
    (hS : p.support ⊆ S) : ∑ a ∈ p.support, f a (coeff a p) = ∑ a ∈ S, f a (coeff a p) := by
  refine Finset.sum_subset hS fun a _ ha => ?_
  rw [MvPolynomial.notMem_support_iff.mp ha, h0]
end Formalism.IncomingBounds.Cay
