-- Prove2me | solution 1 for DeciSigma1.Full.Reduction.mem_seedHull
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:07:28.486632+00:00
-- url     : https://prove2.me/submissions/784c94ad-bc76-4051-871d-d170bc3fad7b

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_RegularCones
public import Definitions.Def_LeanPool_DeciSigma1_Full_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
public import Theorems.Thm_DeciSigma1_Full_Closure_mem_leastClosure


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Reduction
open DeciSigma1.Constraints DeciSigma1.Full.Closure
open DeciSigma1.Semantics DeciSigma1.Automata
variable {n k : Nat} {V : Type} [Fintype V] [DecidableEq V]
variable {c : Fin n → Bool} {Γ : List (LitT n V)}
omit [Fintype V] [DecidableEq V]
namespace DeciSigma1.Full.Reduction
theorem _root_.solution (A : Fin k → Closure.Config n V) (z : Closure.Config n V) :
    z ∈ hull c Γ (Set.range A) ↔ z ∈ leastClosure c Γ ∨ ∃ i, Reach c Γ (A i) z := by
  constructor
  · rintro ⟨a, hf | ⟨i, rfl⟩, hr⟩
    · exact Or.inl (mem_leastClosure.mpr ⟨a, hf, hr⟩)
    · exact Or.inr ⟨i, hr⟩
  · rintro (hm | ⟨i, hr⟩)
    · obtain ⟨a, hf, hr⟩ := mem_leastClosure.mp hm
      exact ⟨a, Or.inl hf, hr⟩
    · exact ⟨A i, Or.inr ⟨i, rfl⟩, hr⟩
end DeciSigma1.Full.Reduction
