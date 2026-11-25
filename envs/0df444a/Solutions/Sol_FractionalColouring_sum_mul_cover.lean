-- Prove2me | solution 1 for FractionalColouring.sum_mul_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:34:48.31388+00:00
-- url     : https://prove2.me/submissions/7ff5a367-c1b3-4401-8812-bb81b78c29d7

module
public import Mathlib
public import Definitions.Def_FractionalLib_FiniteLPDuality
public import Definitions.Def_FractionalLib_Basic
public import Theorems.Thm_FiniteLP_toE_apply
attribute [local simp] FiniteLP.toE_apply



set_option autoImplicit true
@[expose] public section
public section
open Finset
open FractionalColouring
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable {G}
namespace FractionalColouring
theorem _root_.solution (g : V → ℝ) (x : Finset V → ℝ) (T : Finset V) :
    ∑ v ∈ T, g v * ∑ s ∈ univ.filter (fun s => v ∈ s), x s =
      ∑ s, x s * ∑ v ∈ T ∩ s, g v := by
  calc ∑ v ∈ T, g v * ∑ s ∈ univ.filter (fun s => v ∈ s), x s
        = ∑ v ∈ T, ∑ s, if v ∈ s then g v * x s else 0 := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [Finset.sum_filter, Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ => by split_ifs <;> simp
    _ = ∑ s, ∑ v ∈ T, if v ∈ s then g v * x s else 0 := Finset.sum_comm
    _ = ∑ s, x s * ∑ v ∈ T ∩ s, g v := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.mul_sum]
          exact Finset.sum_congr rfl fun v _ => by ring
end FractionalColouring
