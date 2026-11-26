-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sum_residueFiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:26:19.256595+00:00
-- url     : https://prove2.me/submissions/55cb836d-0d88-43b8-82b1-73b26b438afe

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalQuotientOrder
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil



set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    (W : Finset α) (A : α → ℕ) (m : ℕ) (hm : 0 < m) (f : α → β) :
    (∑ a : Fin m, ∑ x ∈ residueFiber W A m a, f x) =
      ∑ x ∈ W, f x := by
  classical
  simp only [residueFiber, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  let a₀ : Fin m := ⟨A x % m, Nat.mod_lt _ hm⟩
  change
    (∑ a ∈ (Finset.univ : Finset (Fin m)),
      if A x % m = (a : ℕ) then f x else 0) = f x
  change
    (∑ a : Fin m, if A x % m = (a : ℕ) then f x else 0) = f x
  calc
    (∑ a : Fin m, if A x % m = (a : ℕ) then f x else 0) =
        (∑ a : Fin m, if a₀ = a then f x else 0) := by
      apply Fintype.sum_congr
      intro a
      by_cases hres : A x % m = (a : ℕ)
      · have ha : a₀ = a := by
          apply Fin.ext
          change A x % m = (a : ℕ)
          exact hres
        simp [hres, ha]
      · have ha : a₀ ≠ a := by
          intro ha
          apply hres
          change A x % m = (a : ℕ)
          exact congrArg Fin.val ha
        simp [hres, ha]
    _ = f x := by
      simpa using Fintype.sum_ite_eq a₀ (fun _ : Fin m => f x)
end CollatzEndpointTransport.FixedTotal
