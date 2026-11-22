-- Prove2me | solution 1 for DeciSigma1.Full.Reduction.seedConsistency_hull_isSolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:26:21.249836+00:00
-- url     : https://prove2.me/submissions/e4fba0a7-4913-4669-b574-ea89b2b1d47b

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_RegularCones
public import Definitions.Def_LeanPool_DeciSigma1_Full_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
public import Theorems.Thm_DeciSigma1_Full_Reduction_crossClash_iff_collision
public import Theorems.Thm_DeciSigma1_Full_Reduction_mem_seedHull
public import Theorems.Thm_DeciSigma1_Full_Reduction_SeedConsistency_live
public import Theorems.Thm_DeciSigma1_Full_Closure_hull_closed
public import Theorems.Thm_DeciSigma1_Full_Closure_hull_facts
public import Theorems.Thm_DeciSigma1_Full_Closure_live_iff
public import Theorems.Thm_DeciSigma1_Full_Closure_mem_seedClosure
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
theorem _root_.solution (hs : ∃ ρ, SatT c ρ Γ) {A B : Fin k → Closure.Config n V}
    (h : SeedConsistency c Γ A B) : IsSolution c Γ (hull c Γ (Set.range A)) := by
  have hμ := sat_iff_leastClosure.mp hs
  have hCl (i : Fin k) := live_iff.mp (h.live hs i)
  refine ⟨hull_closed _, (fun {_} => hull_facts _), ?_, ?_⟩
  · intro z hz hn
    rcases (mem_seedHull A z).mp hz with hm | ⟨i, hr⟩
    · exact hμ.1 hm hn
    · exact (hCl i).1 (mem_seedClosure.mpr (Or.inr hr)) hn
  · intro x y hxy hx hy
    cases hxy with
    | pair v w =>
      rcases (mem_seedHull A _).mp hx with hm | ⟨i, hr⟩ <;>
        rcases (mem_seedHull A _).mp hy with hm' | ⟨j, hr'⟩
      · exact hμ.2 (.pair v w) hm hm'
      · exact (hCl j).2 (.pair v w) (mem_seedClosure.mpr (Or.inl hm))
          (mem_seedClosure.mpr (Or.inr hr'))
      · exact (hCl i).2 (.pair v w) (mem_seedClosure.mpr (Or.inr hr))
          (mem_seedClosure.mpr (Or.inl hm'))
      · by_cases hij : i = j
        · subst j
          exact (hCl i).2 (.pair v w) (mem_seedClosure.mpr (Or.inr hr))
            (mem_seedClosure.mpr (Or.inr hr'))
        · exact h.2.2.2 i j hij
            ((crossClash_iff_collision (A i) (A j) (h.1 i).1 (h.1 j).1).mp
              ⟨v, false, w, hr, hr'⟩)
end DeciSigma1.Full.Reduction
