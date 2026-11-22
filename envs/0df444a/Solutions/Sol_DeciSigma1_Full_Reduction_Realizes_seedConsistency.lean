-- Prove2me | solution 1 for DeciSigma1.Full.Reduction.Realizes.seedConsistency
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:24:28.633837+00:00
-- url     : https://prove2.me/submissions/4f09dbf0-292b-44fa-8cb8-a5219cddb238

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_RegularCones
public import Definitions.Def_LeanPool_DeciSigma1_Full_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
public import Theorems.Thm_DeciSigma1_Full_Reduction_Event_reach
public import Theorems.Thm_DeciSigma1_Full_Reduction_crossClash_iff_collision
public import Theorems.Thm_DeciSigma1_Full_Closure_Consistent_not_flip
public import Theorems.Thm_DeciSigma1_Full_Closure_Reach_mem_of_closed
public import Theorems.Thm_DeciSigma1_Full_Closure_leastClosure_subset
public import Theorems.Thm_DeciSigma1_Full_Closure_not_live_iff_unaryObstruction_or_selfCollision
public import Theorems.Thm_DeciSigma1_Full_Closure_sat_iff_isSolution
public import Theorems.Thm_DeciSigma1_Full_Closure_sat_iff_leastClosure


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Reduction
open DeciSigma1.Constraints DeciSigma1.Full.Closure
open DeciSigma1.Semantics DeciSigma1.Automata
variable {n k : Nat} {V : Type} [Fintype V] [DecidableEq V]
variable {c : Fin n → Bool} {Γ : List (LitT n V)}
namespace DeciSigma1.Full.Reduction
namespace Realizes
theorem _root_.solution {A B : Fin k → Closure.Config n V}
    (h : Realizes c Γ A B) : SeedConsistency c Γ A B := by
  obtain ⟨ρ, hρ, hab⟩ := h
  have hS := (sat_iff_isSolution ρ).mp hρ
  have hl (i : Fin k) : Live c Γ (A i) := ⟨_, hS, (hab i).1⟩
  have hL (i : Fin k) :
      ¬ HasUnaryObstruction c Γ ((A i).1, (A i).2.1) (A i).2.2 ∧
      ¬ ∃ s t, SelfCollisionEvent c Γ ((A i).1, (A i).2.1) (A i).2.2 s t := by
    have hd := (not_live_iff_unaryObstruction_or_selfCollision (sat_iff_leastClosure.mp ⟨ρ, hρ⟩)
      (p := ((A i).1, (A i).2.1)) (u := (A i).2.2))
    exact ⟨fun h => hd.mpr (Or.inl h) (hl i), fun h => hd.mpr (Or.inr h) (hl i)⟩
  refine ⟨hL, fun i hm => (hab i).2 (leastClosure_subset hS hm),
    fun j i he => (hab i).2 (he.reach.mem_of_closed hS.closed (hab j).1), ?_⟩
  intro j i _ hc
  obtain ⟨v, s, w, hr, hr'⟩ :=
    (crossClash_iff_collision (A j) (A i) (hL j).1 (hL i).1).mpr hc
  exact hS.consistent.not_flip (hr.mem_of_closed hS.closed (hab j).1)
    (hr'.mem_of_closed hS.closed (hab i).1)
end Realizes
end DeciSigma1.Full.Reduction
