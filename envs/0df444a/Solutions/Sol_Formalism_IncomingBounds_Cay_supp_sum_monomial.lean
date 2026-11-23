-- Prove2me | solution 1 for Formalism.IncomingBounds.Cay.supp_sum_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:39.28319+00:00
-- url     : https://prove2.me/submissions/efb0b51c-4fb0-4c48-8d71-4d8b5e3990b1

import Definitions.Def_Formalism_IncomingBounds_StatementThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley
import Theorems.Thm_Formalism_IncomingBounds_Cay_supp_sum_superset

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
theorem _root_.solution (h0 : ∀ a, f a 0 = 0) (s : σ →₀ ℕ) (c : K) :
    ∑ a ∈ (monomial s c).support, f a (coeff a (monomial s c)) = f s c := by
  classical
  rw [supp_sum_superset f h0 _ {s} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
    coeff_monomial, if_pos rfl]
end Formalism.IncomingBounds.Cay
