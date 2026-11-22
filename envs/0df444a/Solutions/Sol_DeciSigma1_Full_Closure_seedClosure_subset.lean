-- Prove2me | solution 1 for DeciSigma1.Full.Closure.seedClosure_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:41:55.368227+00:00
-- url     : https://prove2.me/submissions/2f7bf697-233e-46a5-a7e0-84b768accdd1

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
public import Theorems.Thm_DeciSigma1_Full_Closure_hull_least

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}
namespace DeciSigma1.Full.Closure
theorem _root_.solution {S : Set (Config n V)} {a : Config n V}
    (hS : IsSolution c Γ S) (ha : a ∈ S) : seedClosure c Γ a ⊆ S :=
  hull_least hS.closed hS.facts (Set.singleton_subset_iff.mpr ha)
end DeciSigma1.Full.Closure
