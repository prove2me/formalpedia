-- Prove2me | solution 1 for DiracCycle.isPath_reverse_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:52:51.470278+00:00
-- url     : https://prove2.me/submissions/da24e44b-27b3-46cd-813c-c1e6131ac32c

module
public import Mathlib
public import Definitions.Def_MengerHamilton_ChvatalErdosAux
public import Definitions.Def_DiracCycleLib_DiracCycle

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open DiracCycle
open Hamiltonicity
variable {V : Type*} {G : SimpleGraph V}
namespace DiracCycle
theorem _root_.solution {x u v : V} (P₁ : G.Walk x u) (P₂ : G.Walk x v) (h₁ : P₁.IsPath)
    (h₂ : P₂.IsPath) (hdisj : ∀ y ∈ P₁.support, y ∈ P₂.support → y = x) :
    (P₁.reverse.append P₂).IsPath := by
  rw [Walk.isPath_def, Walk.support_append, Walk.support_reverse, List.nodup_append]
  refine ⟨List.nodup_reverse.2 h₁.support_nodup, h₂.support_nodup.sublist (List.tail_sublist _),
    ?_⟩
  intro a ha b hb hab
  subst hab
  rw [List.mem_reverse] at ha
  have hax := hdisj a ha (List.mem_of_mem_tail hb)
  subst hax
  have hn := h₂.support_nodup
  rw [← Walk.cons_tail_support, List.nodup_cons] at hn
  exact hn.1 hb
end DiracCycle
