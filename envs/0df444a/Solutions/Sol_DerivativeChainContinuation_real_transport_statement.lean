-- Prove2me | solution 1 for DerivativeChainContinuation.real_transport_statement
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T17:57:16.879607+00:00
-- url     : https://prove2.me/submissions/2968794d-151b-4f3b-96cb-7877de8462af

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainContinuation_RealTransportStatement
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_full_real_transport_theorem
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators



theorem explicitEndpointCost_eq {n : ℕ} (a : Fin (n+1) → ℂ) (v : ℂ) :
    explicitEndpointCost a v=complexEndpointCost a v := by
  simp only [explicitEndpointCost,complexEndpointCost,DerivativeChainPrivate.IsChain,
    DerivativeChainPrivate.row,DerivativeChainPrivate.fromRoots,DerivativeChainPrivate.chainCost,
    Nat.add_sub_add_right,Nat.add_sub_cancel]
  rfl




end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution {n : ℕ} (a : Fin (n+1) → ℂ)
    (hline : ∃ o c : ℂ,c≠0 ∧ ∃ r : Fin (n+1) → ℝ,∀ i,a i=o+c*(r i : ℂ))
    (hvariance : 0 < ∑ i,‖a i-(∑ j,a j)/(n+1 : ℂ)‖^2) :
    (∑ i,(explicitEndpointCost a (a i))^2)/
      (∑ i,‖a i-(∑ j,a j)/(n+1 : ℂ)‖^2) ≤ (28/3 : ℝ) := by
  have h := (full_real_transport_theorem a hline hvariance).2
  simpa only [explicitEndpointCost_eq,uniformComplexTransportRatio,complexCentroid] using h
