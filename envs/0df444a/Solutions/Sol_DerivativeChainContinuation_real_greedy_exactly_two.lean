-- Prove2me | solution 1 for DerivativeChainContinuation.real_greedy_exactly_two
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:59:10.944995+00:00
-- url     : https://prove2.me/submissions/2e170248-b066-4651-9782-e7d1880f3d75

import Mathlib
import Definitions.Def_DerivativeChainContinuation_GreedyActual
import Definitions.Def_DerivativeChainContinuation_GreedyReal
import Definitions.Def_DerivativeChainContinuation_GreedyStatement
import Definitions.Def_DerivativeChainContinuation_RealTower
import Definitions.Def_DerivativeChainContinuation_RealTransportGeneral
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_real_greedy_all_histories
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators


theorem solution (n : ℕ) (hn : 1≤n) (a : Fin (n+1) → ℝ)
    (hspan : orderedSource a 0<orderedSource a (Fin.last n)) :
    ∃ zL zR : Fin (n+1) → ℂ, zL≠zR ∧
      ∀ z : Fin (n+1) → ℂ, IsGreedyChain (fun i => (a i : ℂ)) z ↔
        z=zL ∨ z=zR := by
  obtain ⟨r,hr,hm,hs,hrows,hclass,hcost,hex⟩ := real_greedy_all_histories n hn a
  refine ⟨fun i => (leftRow r i.val : ℂ),fun i => (rightRow r i.val : ℂ),?_,?_⟩
  · intro he
    have h := congrFun he (Fin.last n)
    change (r n 0 : ℂ)=(r n (Fin.last n) : ℂ) at h
    rw [hr] at h
    have h' : orderedSource a 0=orderedSource a (Fin.last n) := Complex.ofReal_injective h
    exact (ne_of_lt hspan) h'
  · intro z
    rw [hclass z]
    constructor
    · rintro (hl | hrr)
      · exact Or.inl (funext hl)
      · exact Or.inr (funext hrr)
    · rintro (rfl | rfl)
      · exact Or.inl (fun _ => rfl)
      · exact Or.inr (fun _ => rfl)
