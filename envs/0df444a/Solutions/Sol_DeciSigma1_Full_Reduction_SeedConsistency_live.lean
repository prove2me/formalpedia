-- Prove2me | solution 1 for DeciSigma1.Full.Reduction.SeedConsistency.live
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:24:30.394372+00:00
-- url     : https://prove2.me/submissions/58e7bbc5-3284-4fa6-b954-4298a88170df

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_RegularCones
public import Definitions.Def_LeanPool_DeciSigma1_Full_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
public import Theorems.Thm_DeciSigma1_Full_Closure_not_live_iff_unaryObstruction_or_selfCollision
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
namespace SeedConsistency
theorem _root_.solution (hs : ∃ ρ, SatT c ρ Γ) {A B : Fin k → Closure.Config n V}
    (h : SeedConsistency c Γ A B) (i : Fin k) : Live c Γ (A i) := by
  by_contra hn
  rcases (not_live_iff_unaryObstruction_or_selfCollision (sat_iff_leastClosure.mp hs)
    (p := ((A i).1, (A i).2.1)) (u := (A i).2.2)).mp hn with hd | he
  · exact (h.1 i).1 hd
  · exact (h.1 i).2 he
end SeedConsistency
end DeciSigma1.Full.Reduction
