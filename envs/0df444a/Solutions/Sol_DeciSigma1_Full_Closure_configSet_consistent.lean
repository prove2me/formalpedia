-- Prove2me | solution 1 for DeciSigma1.Full.Closure.configSet_consistent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:42:25.342986+00:00
-- url     : https://prove2.me/submissions/14acfd25-f2a7-4f65-9ff8-7ef374cf5a86

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
public import Theorems.Thm_DeciSigma1_Full_Closure_leaf_disjoint

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Semantics
open DeciSigma1.Constraints
variable {n : ℕ}
variable {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}
namespace DeciSigma1.Full.Closure
theorem _root_.solution (ρ : V → Semantics.Tree n) : Consistent (configSet c ρ) := by
  intro p q h hp hq
  cases h with
  | pair v w => exact leaf_disjoint c (ρ v) w hp hq
end DeciSigma1.Full.Closure
