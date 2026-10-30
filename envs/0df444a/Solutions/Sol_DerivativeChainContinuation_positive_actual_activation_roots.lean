-- Prove2me | solution 1 for DerivativeChainContinuation.positive_actual_activation_roots
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:24:29.449806+00:00
-- url     : https://prove2.me/submissions/d06ced95-3667-4fce-b605-677d616d2830

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PositiveSpokeClosure
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_positive_spoke_activation_root_power
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators

theorem actual_complex_source_natDegree {n : ℕ} (a : Fin (n+1) → ℂ) :
    (fromRoots a).natDegree=n+1 := by
  simp only [fromRoots]
  rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (a i))]
  simp
























end DerivativeChainContinuation

theorem solution {n : ℕ} (a : Fin (n+1) → ℂ)
    (k r : ℕ) (Q : Polynomial ℝ) (hk : 2 ≤ k) (hQ : PositiveQuotient Q)
    (hQdegree : 0<Q.natDegree) (hp : fromRoots a=spokePoly k r Q) :
    ∃ b : ℝ,0<b ∧ ∀ z : ℂ,(row a k).eval z=0 ↔ z^k=(b : ℂ) := by
  have hd : (spokePoly k r Q).natDegree=n+1 := by rw [←hp,actual_complex_source_natDegree]
  simpa only [row,hp] using positive_spoke_activation_root_power n k r Q hk hQ hQdegree hd
