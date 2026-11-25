-- Prove2me | solution 1 for BayesianPersuasion.Proof.joint_eq_zero_of_null
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:07:20.999472+00:00
-- url     : https://prove2.me/submissions/9af3d7fd-9401-498b-8c4f-e8d96a7ee949

module
public import Definitions.Def_BayesianPersuasion_Primitives
public import Mathlib.Tactic
public import Definitions.Def_BayesianPersuasion_Signals

set_option autoImplicit true
@[expose] public section
public section
universe uΩ uA
open Set Finset
open BayesianPersuasion
variable {Ω : Type uΩ} [Fintype Ω]
open BayesianPersuasion.Proof
namespace BayesianPersuasion.Proof
theorem _root_.solution (p : Belief Ω) {n : ℕ} (π : Signal Ω n)
    (s : Fin n) (hs : signalMass p π s = 0) (ω : Ω) : p.val ω * (π ω).val s = 0 := by
  apply le_antisymm _ (mul_nonneg (p.property.1 ω) ((π ω).property.1 s))
  calc
    _ ≤ signalMass p π s := Finset.single_le_sum
      (fun ω _ => mul_nonneg (p.property.1 ω) ((π ω).property.1 s)) (mem_univ ω)
    _ = 0 := hs
end BayesianPersuasion.Proof
