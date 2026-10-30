-- Prove2me | solution 1 for DerivativeChainContinuation.full_real_transport_theorem
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T17:54:49.903241+00:00
-- url     : https://prove2.me/submissions/41c778d3-ba17-4284-bf3f-4756f0640113

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainContinuation_RealTransportComplete
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_collinear_real_transport_theorem
import Theorems.Thm_DerivativeChainContinuation_collinear_transport_chain_family
import Theorems.Thm_DerivativeChainContinuation_complexEndpointCost_attained
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators


open DerivativeChainContinuation in
theorem solution {n : ℕ} (a : Fin (n+1) → ℂ)
    (hline : OnComplexLine a)
    (hvariance : 0 < ∑ i,‖a i-complexCentroid a‖^2) :
    (∀ j,∃ z : Fin (n+1) → ℂ,IsChain a z ∧ z (Fin.last n)=a j ∧
      chainCost z=complexEndpointCost a (a j)) ∧
    uniformComplexTransportRatio a ≤ (28/3 : ℝ) := by
  have hn : 0<n := by
    by_contra h
    have hn0 : n=0 := by omega
    subst n
    simp [complexCentroid] at hvariance
  obtain ⟨o,c,hc,r,hr⟩ := hline
  have ha : a=(fun i => o+c*(r i : ℂ)) := funext hr
  subst a
  constructor
  · obtain ⟨z,hz,he,_⟩ := collinear_transport_chain_family n hn r o c hc
    intro j
    exact complexEndpointCost_attained _ _ ⟨z j,hz j,he j⟩
  · exact collinear_real_transport_theorem n hn r o c hc hvariance
