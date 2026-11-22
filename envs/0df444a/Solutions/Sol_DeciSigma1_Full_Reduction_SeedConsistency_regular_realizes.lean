-- Prove2me | solution 1 for DeciSigma1.Full.Reduction.SeedConsistency.regular_realizes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:27:30.777909+00:00
-- url     : https://prove2.me/submissions/089b246f-6afd-40e3-bd8b-2be287f883e9

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_RegularCones
public import Definitions.Def_LeanPool_DeciSigma1_Full_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
public import Theorems.Thm_DeciSigma1_Full_Reduction_reach_iff_event
public import Theorems.Thm_DeciSigma1_Full_Reduction_mem_seedHull
public import Theorems.Thm_DeciSigma1_Full_Reduction_seedHull_cone_regular
public import Theorems.Thm_DeciSigma1_Full_Reduction_seedConsistency_hull_isSolution
public import Theorems.Thm_DeciSigma1_Full_Closure_isSolution_iff_assignment
public import Theorems.Thm_DeciSigma1_Full_Closure_regular_of_leaf
public import Theorems.Thm_DeciSigma1_Full_Closure_subset_hull


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Reduction
open DeciSigma1.Constraints DeciSigma1.Full.Closure
open DeciSigma1.Semantics DeciSigma1.Automata
variable {n k : Nat} {V : Type} [Fintype V] [DecidableEq V]
variable {c : Fin n → Bool} {Γ : List (LitT n V)}
namespace DeciSigma1.Full.Reduction
namespace SeedConsistency
theorem _root_.solution (hs : ∃ ρ, SatT c ρ Γ)
    {A B : Fin k → Closure.Config n V} (h : SeedConsistency c Γ A B) :
    ∃ ρ, (∀ v, Models.RegularTop (ρ v)) ∧ SatT c ρ Γ ∧ ∀ i,
      A i ∈ configSet c ρ ∧ B i ∉ configSet c ρ := by
  obtain ⟨ρ, hρ, heq⟩ := isSolution_iff_assignment.mp (seedConsistency_hull_isSolution hs h)
  refine ⟨ρ, ?_, hρ, ?_⟩
  · intro v
    apply regular_of_leaf c
    intro s
    have hc : leaf c (ρ v) s = {t | (v, s, t) ∈ hull c Γ (Set.range A)} := by
      ext t
      change (v, s, t) ∈ configSet c ρ ↔ _
      rw [heq]
      rfl
    rw [hc]
    exact seedHull_cone_regular h (v, s)
  · intro i
    rw [heq]
    refine ⟨subset_hull _ ⟨i, rfl⟩, ?_⟩
    intro hb
    rcases (mem_seedHull A (B i)).mp hb with hm | ⟨j, hr⟩
    · exact h.2.1 i hm
    · exact h.2.2.1 j i ((reach_iff_event (A j) (B i) (h.1 j).1).mp hr)
end SeedConsistency
end DeciSigma1.Full.Reduction
