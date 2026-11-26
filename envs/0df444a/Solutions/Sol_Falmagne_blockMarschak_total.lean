-- Prove2me | solution 1 for Falmagne.blockMarschak_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:26:19.450071+00:00
-- url     : https://prove2.me/submissions/2d87dcf9-530e-43f8-bf36-ff1c80ec1f0a

module
public import Definitions.Def_EconomicsNextProof_Basic
public import Definitions.Def_EconomicsNextProof_Mobius
public import Definitions.Def_EconomicsNextProof_Path
public import Definitions.Def_EconomicsNextProof_Conservation
public import Theorems.Thm_EconomicsNextProof_upperMobius_const


set_option autoImplicit true
@[expose] public section
public section
open Falmagne
open Finset
open EconomicsNextProof
variable {X : Type*} [Fintype X] [DecidableEq X]
namespace Falmagne
theorem _root_.solution (p : Finset X → X → ℝ) (hp : IsChoiceRule p)
    (A : Finset X) (hA : A.Nonempty) :
    ∑ x : X, blockMarschak p x A = if A = univ then 1 else 0 := by
  have hnorm (B : Finset X) (hAB : A ⊆ B) : (∑ x : X, p B x) = 1 := by
    calc
      (∑ x : X, p B x) = ∑ x ∈ B, p B x := by
        symm
        exact sum_subset (subset_univ B) (fun x _ hx => hp.2.1 B x hx)
      _ = 1 := hp.2.2 B (hA.mono hAB)
  unfold blockMarschak upperMobius
  rw [sum_comm]
  calc
    (∑ B ∈ univ.filter (fun B : Finset X => A ⊆ B),
        ∑ x : X, (-1 : ℝ) ^ (B \ A).card * p B x) =
      ∑ B ∈ univ.filter (fun B : Finset X => A ⊆ B),
        (-1 : ℝ) ^ (B \ A).card * 1 := by
      apply sum_congr rfl
      intro B hB
      rw [← mul_sum, hnorm B (mem_filter.mp hB).2]
    _ = if A = univ then 1 else 0 := upperMobius_const 1 A
end Falmagne
