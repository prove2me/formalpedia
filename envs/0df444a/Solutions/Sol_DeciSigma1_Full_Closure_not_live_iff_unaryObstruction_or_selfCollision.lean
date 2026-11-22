-- Prove2me | solution 1 for DeciSigma1.Full.Closure.not_live_iff_unaryObstruction_or_selfCollision
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:23:07.718808+00:00
-- url     : https://prove2.me/submissions/b0b735f9-c597-4832-8451-6b21c39b07e3

module
public import Mathlib.Data.Fintype.Powerset
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Theorems.Thm_DeciSigma1_Full_Closure_reach_neg_iff
public import Theorems.Thm_DeciSigma1_Full_Closure_selfCollisionEvent_return
public import Theorems.Thm_DeciSigma1_Full_Closure_return_selfCollisionEvent_of_not_hasUnaryObstruction
public import Theorems.Thm_DeciSigma1_Full_Closure_dead_iff


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Automata
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*}
variable [Fintype V] [DecidableEq V]
variable (c : Fin n → Bool) (Γ : List (LitT n V))
variable {c Γ}
variable (c Γ)
variable {c Γ}
namespace DeciSigma1.Full.Closure
theorem _root_.solution
    (hsat : Avoids Γ (leastClosure c Γ) ∧ Consistent (leastClosure c Γ))
    {p : V × Bool} {u : List (Fin n)} :
    ¬ Live c Γ (p.1, p.2, u) ↔
      HasUnaryObstruction c Γ p u ∨ ∃ i j, SelfCollisionEvent c Γ p u i j := by
  classical
  rw [dead_iff hsat]
  constructor
  · rintro (hn | hm | ⟨δ, hr⟩)
    · exact Or.inl (Or.inl (reach_neg_iff.mp hn))
    · exact Or.inl (Or.inr hm)
    · by_cases hd : HasUnaryObstruction c Γ p u
      · exact Or.inl hd
      · exact Or.inr (return_selfCollisionEvent_of_not_hasUnaryObstruction hd hr)
  · rintro ((hn | hm) | ⟨i, j, hs⟩)
    · exact Or.inl (reach_neg_iff.mpr hn)
    · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr (selfCollisionEvent_return hs))
end DeciSigma1.Full.Closure
