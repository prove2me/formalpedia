-- Prove2me | solution 1 for Formalism.IncomingBounds.Cay.supp_sum_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:39.291591+00:00
-- url     : https://prove2.me/submissions/d3a9e4ea-a3a9-4e8b-b828-dfb9a919be4f

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
theorem _root_.solution (h0 : ∀ a, f a 0 = 0) (hadd : ∀ a x y, f a (x + y) = f a x + f a y)
    (p q : MvPolynomial σ K) :
    ∑ a ∈ (p + q).support, f a (coeff a (p + q)) =
      ∑ a ∈ p.support, f a (coeff a p) + ∑ a ∈ q.support, f a (coeff a q) := by
  classical
  have hpq : (p + q).support ⊆ p.support ∪ q.support := fun a ha => by
    rw [Finset.mem_union]
    by_contra hn
    rw [not_or] at hn
    rw [MvPolynomial.mem_support_iff, coeff_add, MvPolynomial.notMem_support_iff.mp hn.1,
      MvPolynomial.notMem_support_iff.mp hn.2, add_zero] at ha
    exact ha rfl
  rw [supp_sum_superset f h0 (p + q) (p.support ∪ q.support) hpq,
    supp_sum_superset f h0 p (p.support ∪ q.support) (fun _ h => Finset.mem_union_left _ h),
    supp_sum_superset f h0 q (p.support ∪ q.support) (fun _ h => Finset.mem_union_right _ h),
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by rw [coeff_add, hadd]
end Formalism.IncomingBounds.Cay
