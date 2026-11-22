-- Prove2me | solution 1 for DeciSigma1.Full.Reduction.SeedConsistency.realizes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:29:04.519676+00:00
-- url     : https://prove2.me/submissions/dd7494ae-1702-4b79-9eac-e51c39c32f73

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_RegularCones
public import Definitions.Def_LeanPool_DeciSigma1_Full_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
public import Theorems.Thm_DeciSigma1_Full_Reduction_SeedConsistency_regular_realizes

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
    (h : SeedConsistency c Γ A B) : Realizes c Γ A B := by
  obtain ⟨ρ, _, ht, hw⟩ := h.regular_realizes hs
  exact ⟨ρ, ht, hw⟩
end SeedConsistency
end DeciSigma1.Full.Reduction
