-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.affine_index_dist_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:58:13.584459+00:00
-- url     : https://prove2.me/submissions/aa5de584-71a8-4fa5-8d4e-4b08f6553f63

import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_zero
attribute [local simp] CollatzEndpointTransport.Terras.integerCorrection_zero

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution
    {A D q r i j : ℕ}
    (hA : D ≤ A) (hq : q < A) (hr : r < A)
    (hclose : (A * i + q).dist (A * j + r) < D) :
    i.dist j ≤ 1 := by
  by_contra hnot
  have htwo : 2 ≤ i.dist j := by omega
  rcases le_total i j with hij | hji
  · have hgap : i + 2 ≤ j := by
      rw [Nat.dist_eq_sub_of_le hij] at htwo
      omega
    have hsep : A * i + q + A ≤ A * j + r := by
      calc
        A * i + q + A ≤ A * i + A + A := by omega
        _ = A * (i + 2) := by ring
        _ ≤ A * j := Nat.mul_le_mul_left A hgap
        _ ≤ A * j + r := Nat.le_add_right _ _
    have hle : A * i + q ≤ A * j + r :=
      le_trans (Nat.le_add_right _ A) hsep
    have hlower : A ≤ (A * i + q).dist (A * j + r) := by
      rw [Nat.dist_eq_sub_of_le hle]
      exact Nat.le_sub_of_add_le (by
        simpa [add_comm, add_left_comm, add_assoc] using hsep)
    exact (not_lt_of_ge (hA.trans hlower)) hclose
  · have hgap : j + 2 ≤ i := by
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hji] at htwo
      omega
    have hsep : A * j + r + A ≤ A * i + q := by
      calc
        A * j + r + A ≤ A * j + A + A := by omega
        _ = A * (j + 2) := by ring
        _ ≤ A * i := Nat.mul_le_mul_left A hgap
        _ ≤ A * i + q := Nat.le_add_right _ _
    have hle : A * j + r ≤ A * i + q :=
      le_trans (Nat.le_add_right _ A) hsep
    have hlower : A ≤ (A * i + q).dist (A * j + r) := by
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hle]
      exact Nat.le_sub_of_add_le (by
        simpa [add_comm, add_left_comm, add_assoc] using hsep)
    exact (not_lt_of_ge (hA.trans hlower)) hclose
end CollatzEndpointTransport.Terras
