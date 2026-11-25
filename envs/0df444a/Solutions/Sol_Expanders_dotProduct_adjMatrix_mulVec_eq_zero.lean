-- Prove2me | solution 1 for Expanders.dotProduct_adjMatrix_mulVec_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:29:43.469823+00:00
-- url     : https://prove2.me/submissions/5940f0cb-6b8e-4c83-9548-8022e8ccc55c

module
public import Mathlib
public import Definitions.Def_ExpanderLib_NilliBall
public import Theorems.Thm_Expanders_dotProduct_adjMatrix_mulVec

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open Expanders
variable {V : Type*} [Fintype V]
namespace Expanders
theorem _root_.solution (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V → ℝ) (B₁ B₂ : Finset V) (hx : ∀ v, v ∉ B₁ → x v = 0) (hy : ∀ v, v ∉ B₂ → y v = 0)
    (hno : ∀ a ∈ B₁, ∀ b ∈ B₂, ¬ G.Adj a b) :
    dotProduct x (G.adjMatrix ℝ *ᵥ y) = 0 := by
  rw [dotProduct_adjMatrix_mulVec]
  refine Finset.sum_eq_zero (fun v _ => ?_)
  by_cases hv : v ∈ B₁
  · rw [Finset.sum_eq_zero, mul_zero]
    intro w hw
    rw [mem_neighborFinset] at hw
    exact hy w (fun hw2 => hno v hv w hw2 hw)
  · rw [hx v hv, zero_mul]
end Expanders
