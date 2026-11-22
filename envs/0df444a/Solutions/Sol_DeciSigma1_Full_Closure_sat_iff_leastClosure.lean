-- Prove2me | solution 1 for DeciSigma1.Full.Closure.sat_iff_leastClosure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:45:16.232039+00:00
-- url     : https://prove2.me/submissions/0f909fbb-d5ae-453c-8ae6-7d68f44cefa6

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
public import Theorems.Thm_DeciSigma1_Full_Closure_sat_iff_isSolution
public import Theorems.Thm_DeciSigma1_Full_Closure_isSolution_iff_assignment
public import Theorems.Thm_DeciSigma1_Full_Closure_hull_closed
public import Theorems.Thm_DeciSigma1_Full_Closure_hull_facts
public import Theorems.Thm_DeciSigma1_Full_Closure_leastClosure_subset

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}
namespace DeciSigma1.Full.Closure
theorem _root_.solution :
    (∃ ρ, SatT c ρ Γ) ↔ Avoids Γ (leastClosure c Γ) ∧ Consistent (leastClosure c Γ) := by
  constructor
  · rintro ⟨ρ, hρ⟩
    have hS := (sat_iff_isSolution ρ).mp hρ
    have hsub := leastClosure_subset hS
    exact ⟨fun {_} hp => hS.avoids (hsub hp),
      fun {_ _} h hp hq => hS.consistent h (hsub hp) (hsub hq)⟩
  · rintro ⟨hn, hd⟩
    obtain ⟨ρ, hρ, _⟩ := isSolution_iff_assignment.mp
      (show IsSolution c Γ (leastClosure c Γ) from
        ⟨hull_closed _, (fun {_} => hull_facts _), hn, hd⟩)
    exact ⟨ρ, hρ⟩
end DeciSigma1.Full.Closure
