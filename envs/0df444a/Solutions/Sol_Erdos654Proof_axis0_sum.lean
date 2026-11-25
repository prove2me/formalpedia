-- Prove2me | solution 1 for Erdos654Proof.axis0_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:49:23.124626+00:00
-- url     : https://prove2.me/submissions/6494b8bd-0d2d-40bd-9c4a-64dd55dfddae

module
public import Mathlib
public import Definitions.Def_Erdos654Palomar_Solution
public import Theorems.Thm_Erdos654Proof_dist_sq
public import Theorems.Thm_Erdos654Proof_ext_two

set_option autoImplicit true
@[expose] public section
public section
open scoped EuclideanGeometry Finset
open Filter Finset EuclideanGeometry
open Erdos654Proof
namespace Erdos654Proof
theorem _root_.solution {P Q c : ℝ²} {r : ℝ} (hP : P 1 = 0) (hQ : Q 1 = 0) (hPQ : P ≠ Q)
    (hPr : dist P c = r) (hQr : dist Q c = r) : P 0 + Q 0 = 2 * c 0 := by
  have h0 : P 0 ≠ Q 0 := fun h ↦ hPQ (ext_two h (hP.trans hQ.symm))
  have e := dist_sq P c
  have f := dist_sq Q c
  rw [hPr, hP] at e
  rw [hQr, hQ] at f
  have : (P 0 - Q 0) * (P 0 + Q 0 - 2 * c 0) = 0 := by linear_combination f - e
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h) h0
  · linarith
end Erdos654Proof
