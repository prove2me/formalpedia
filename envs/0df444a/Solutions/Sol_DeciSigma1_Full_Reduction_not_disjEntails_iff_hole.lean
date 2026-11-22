-- Prove2me | solution 1 for DeciSigma1.Full.Reduction.not_disjEntails_iff_hole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:37:12.214699+00:00
-- url     : https://prove2.me/submissions/20dad6d6-35d6-4ca1-92f8-573e46e747c3

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Compile
public import Theorems.Thm_DeciSigma1_Full_Reduction_hasCountermodelIn_iff_exists_hole
public import Theorems.Thm_DeciSigma1_Full_not_disjEntailsIn_iff


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Reduction
open DeciSigma1.Constraints
variable {n k : Nat} {V : Type} [Fintype V] [DecidableEq V]
variable {c : Fin n → Bool} {Γ : List (LitT n V)} {q : Fin k → V × V}
namespace DeciSigma1.Full.Reduction
theorem _root_.solution (hs : ∃ ρ, SatT c ρ Γ) :
    ¬ DisjEntailsIn (fun _ => True) c Γ q ↔
      ∃ m : Fin k → Bool, ∃ W, (compile c Γ q m).IsHole W := by
  rw [not_disjEntailsIn_iff, hasCountermodelIn_iff_exists_hole hs]
end DeciSigma1.Full.Reduction
