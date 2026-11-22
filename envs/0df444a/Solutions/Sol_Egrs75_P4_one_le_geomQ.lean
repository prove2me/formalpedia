-- Prove2me | solution 1 for Egrs75.P4.one_le_geomQ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:41.426088+00:00
-- url     : https://prove2.me/submissions/ddfc645b-b4dc-4e86-9e14-5267b821cfd0

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.GeomSum
public import Definitions.Def_LeanPool_Egrs75_ConditionThreeWindow

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.P4
open Nat
open Finset
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
namespace Egrs75.P4
theorem _root_.solution {q i : ℕ} (hi : 1 ≤ i) : 1 ≤ geomQ q i := by
  unfold geomQ
  have h0 : (0 : ℕ) ∈ Finset.range i := Finset.mem_range.mpr (by omega)
  calc (1 : ℕ) = q ^ 0 := by rw [pow_zero]
    _ ≤ ∑ k ∈ Finset.range i, q ^ k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) h0
end Egrs75.P4
