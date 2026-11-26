-- Prove2me | solution 1 for C6BipartiteDomination.paper9_unique_extra_S_neighbor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:03:30.651797+00:00
-- url     : https://prove2.me/submissions/3e77275f-54b0-4e7c-a129-36b9aeee7953

import Definitions.Def_C6BipartiteDomination_A9
import Definitions.Def_C6BipartiteDomination_PaperSection9
import Theorems.Thm_C6BipartiteDomination_paper9_union_resource_bound

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D T : Finset V} {u q r : V}
    (hT : T ⊆ (SPart G D).filter (fun v => G.Adj u v))
    (hTcard : T.card = 2)
    (hq : q ∈ (SPart G D).filter (fun v => G.Adj u v))
    (hr : r ∈ (SPart G D).filter (fun v => G.Adj u v))
    (hqT : q ∉ T) (hrT : r ∉ T)
    (hs : sCharge G D u ≤ 3) : q = r := by
  classical
  by_contra hqr
  let P : Finset V := {q, r}
  have hPcard : P.card = 2 := by simp [P, hqr]
  have hPsub : P ⊆ (SPart G D).filter (fun v => G.Adj u v) := by
    intro v hv
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hvq | hvr
    · simpa [hvq] using hq
    · simpa [hvr] using hr
  have hdisj : Disjoint T P := by
    rw [Finset.disjoint_left]
    intro v hvT hvP
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hvP
    rcases hvP with hvq | hvr
    · exact hqT (hvq ▸ hvT)
    · exact hrT (hvr ▸ hvT)
  have hbound := paper9_union_resource_bound G hT hPsub hdisj
  rw [hTcard, hPcard] at hbound
  omega
end C6BipartiteDomination
