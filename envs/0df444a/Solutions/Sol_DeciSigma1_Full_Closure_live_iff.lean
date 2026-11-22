-- Prove2me | solution 1 for DeciSigma1.Full.Closure.live_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:43:00.785091+00:00
-- url     : https://prove2.me/submissions/31079829-fd17-4038-999d-b3740f185c30

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
public import Theorems.Thm_DeciSigma1_Full_Closure_hull_closed
public import Theorems.Thm_DeciSigma1_Full_Closure_hull_facts
public import Theorems.Thm_DeciSigma1_Full_Closure_subset_hull
public import Theorems.Thm_DeciSigma1_Full_Closure_seedClosure_subset

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}
namespace DeciSigma1.Full.Closure
theorem _root_.solution {a : Config n V} :
    Live c Γ a ↔ Avoids Γ (seedClosure c Γ a) ∧ Consistent (seedClosure c Γ a) := by
  constructor
  · rintro ⟨S, hS, ha⟩
    have hsub := seedClosure_subset hS ha
    exact ⟨fun {_} hp => hS.avoids (hsub hp),
      fun {_ _} h hp hq => hS.consistent h (hsub hp) (hsub hq)⟩
  · rintro ⟨hn, hd⟩
    exact ⟨seedClosure c Γ a, ⟨hull_closed _, (fun {_} => hull_facts _), hn, hd⟩,
      subset_hull _ (Set.mem_singleton a)⟩
end DeciSigma1.Full.Closure
