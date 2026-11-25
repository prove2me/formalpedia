-- Prove2me | solution 1 for FractionalColouring.sum_le_mul_of_indep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:36:41.935016+00:00
-- url     : https://prove2.me/submissions/525555d3-0f33-4393-b6c4-945fdfc139b3

module
public import Mathlib
public import Definitions.Def_FractionalLib_FiniteLPDuality
public import Definitions.Def_FractionalLib_Basic
public import Theorems.Thm_FractionalColouring_sum_mul_cover
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
theorem _root_.solution {g : V → ℝ} (hg : ∀ v, 0 ≤ g v) {T : Finset V} {c : ℝ}
    (hc : ∀ s : Finset V, G.IsIndepSet (s : Set V) → ∑ v ∈ T ∩ s, g v ≤ c)
    {x : Finset V → ℝ} (hx : IsFracColouring G x) :
    ∑ v ∈ T, g v ≤ c * ∑ s, x s := by
  calc ∑ v ∈ T, g v ≤ ∑ v ∈ T, g v * ∑ s ∈ univ.filter (fun s => v ∈ s), x s :=
        Finset.sum_le_sum fun v _ => le_mul_of_one_le_right (hg v) (hx.2.2 v)
    _ = ∑ s, x s * ∑ v ∈ T ∩ s, g v := sum_mul_cover g x T
    _ ≤ ∑ s, x s * c := by
        refine Finset.sum_le_sum fun s _ => ?_
        by_cases hs : G.IsIndepSet (s : Set V)
        · exact mul_le_mul_of_nonneg_left (hc s hs) (hx.1 s)
        · rw [hx.2.1 s hs]; simp
    _ = c * ∑ s, x s := by rw [← Finset.sum_mul, mul_comm]
end FractionalColouring
