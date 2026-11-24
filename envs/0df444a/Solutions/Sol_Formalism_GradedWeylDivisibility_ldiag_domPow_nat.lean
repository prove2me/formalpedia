-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldiag_domPow_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:15:12.92757+00:00
-- url     : https://prove2.me/submissions/b2a525e1-7ddd-4b4c-9d62-92fe58bcd498

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DomPow
import Theorems.Thm_Formalism_GradedWeylDivisibility_antitone_prod_pow_dominance

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (t : ℕ → ℝ) (ht0 : ∀ a, 0 ≤ t a) (ht : Antitone t) (μ lam : ℕ → ℕ) (N : ℕ)
    (hS : ∀ k ≤ N, ∑ a ∈ range k, μ a ≤ ∑ a ∈ range k, lam a)
    (hT : ∑ a ∈ range N, μ a = ∑ a ∈ range N, lam a) :
    ∏ a ∈ range N, t a ^ μ a ≤ ∏ a ∈ range N, t a ^ lam a := by
  have h := antitone_prod_pow_dominance t ht0 ht μ lam N hS 0 le_rfl (fun a _ => ht0 a)
  rwa [hT, Nat.sub_self, pow_zero, mul_one] at h
end Formalism.GradedWeylDivisibility
