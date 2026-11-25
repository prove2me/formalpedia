-- Prove2me | solution 1 for CliqueMinors.induce_connected_of_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:38:44.762024+00:00
-- url     : https://prove2.me/submissions/20e583cd-66c6-4b6a-9c4a-d615e06b0a87

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}
open Relation
namespace CliqueMinors
theorem _root_.solution (G : SimpleGraph V) (B : Finset V) (r : V) (hr : r ∈ B)
    (h : ∀ v ∈ B, ReflTransGen (InAdj G B) r v) : (G.induce (B : Set V)).Connected := by
  have key : ∀ v, ReflTransGen (InAdj G B) r v → ∀ hv : v ∈ B,
      (G.induce (B : Set V)).Reachable ⟨r, hr⟩ ⟨v, hv⟩ := by
    intro v hrv
    induction hrv with
    | refl => intro _; rfl
    | tail _ hbc ih =>
      intro _
      exact (ih hbc.1).trans (Adj.reachable (by simpa using hbc.2.2))
  rw [connected_iff]
  refine ⟨fun u v => ?_, ⟨⟨r, hr⟩⟩⟩
  exact (key u.1 (h u.1 u.2) u.2).symm.trans (key v.1 (h v.1 v.2) v.2)
end CliqueMinors
