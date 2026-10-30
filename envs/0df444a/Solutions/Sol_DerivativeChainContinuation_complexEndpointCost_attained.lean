-- Prove2me | solution 1 for DerivativeChainContinuation.complexEndpointCost_attained
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T17:52:46.837165+00:00
-- url     : https://prove2.me/submissions/7ad0d141-9435-484f-bc85-ec14690a4b5f

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_finite_derivative_chains
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators


open DerivativeChainContinuation in
theorem solution {n : ℕ} (a : Fin (n+1) → ℂ) (v : ℂ)
    (hex : ∃ z : Fin (n+1) → ℂ,IsChain a z ∧ z (Fin.last n)=v) :
    ∃ z : Fin (n+1) → ℂ,IsChain a z ∧ z (Fin.last n)=v ∧
      chainCost z=complexEndpointCost a v := by
  let S := {z : Fin (n+1) → ℂ | IsChain a z ∧ z (Fin.last n)=v}
  have hs : S.Finite := (finite_derivative_chains a).subset (fun z hz => hz.1)
  have hcost : {t : ℝ | ∃ z : Fin (n+1) → ℂ,
      IsChain a z ∧ z (Fin.last n)=v ∧ chainCost z=t} = chainCost '' S := by
    ext t
    constructor
    · rintro ⟨z,hz,he,ht⟩
      exact ⟨z,⟨hz,he⟩,ht⟩
    · rintro ⟨z,⟨hz,he⟩,ht⟩
      exact ⟨z,hz,he,ht⟩
  have hne : (chainCost '' S).Nonempty := by
    obtain ⟨z,hz,he⟩ := hex
    exact ⟨chainCost z,z,⟨hz,he⟩,rfl⟩
  obtain ⟨t,ht⟩ := (hs.image chainCost).isCompact.exists_isLeast hne
  obtain ⟨z,hz,rfl⟩ := ht.1
  refine ⟨z,hz.1,hz.2,?_⟩
  unfold complexEndpointCost
  rw [hcost,ht.csInf_eq]
