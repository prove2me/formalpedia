-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.quotient_injective_on_residueFiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:26:17.266778+00:00
-- url     : https://prove2.me/submissions/9c003cfd-55bc-4a0a-8dbb-7c08f2656dd5

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
    {α : Type*} [DecidableEq α]
    {W : Finset α} {A : α → ℕ} {m : ℕ} {a : Fin m}
    (hA : Set.InjOn A W) :
    Set.InjOn (fun x => A x / m) (residueFiber W A m a) := by
  intro x hx y hy hq
  apply hA
  · exact (Finset.mem_filter.mp hx).1
  · exact (Finset.mem_filter.mp hy).1
  have hrx : A x % m = a := (Finset.mem_filter.mp hx).2
  have hry : A y % m = a := (Finset.mem_filter.mp hy).2
  change A x / m = A y / m at hq
  calc
    A x = A x % m + m * (A x / m) := (Nat.mod_add_div (A x) m).symm
    _ = A y % m + m * (A y / m) := by simp only [hrx, hry, hq]
    _ = A y := Nat.mod_add_div (A y) m
end CollatzEndpointTransport.FixedTotal
