-- Prove2me | solution 1 for Erdos654Proof.axis1_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:27:15.482808+00:00
-- url     : https://prove2.me/submissions/efaf57d8-6ccd-40d9-8f4e-7a5f966c86f6

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
theorem _root_.solution {P Q c : ℝ²} {r : ℝ} (hP : P 0 = 0) (hQ : Q 0 = 0) (hPQ : P ≠ Q)
    (hPr : dist P c = r) (hQr : dist Q c = r) : P 1 + Q 1 = 2 * c 1 := by
  have h1 : P 1 ≠ Q 1 := fun h ↦ hPQ (ext_two (hP.trans hQ.symm) h)
  have e := dist_sq P c
  have f := dist_sq Q c
  rw [hPr, hP] at e
  rw [hQr, hQ] at f
  have : (P 1 - Q 1) * (P 1 + Q 1 - 2 * c 1) = 0 := by linear_combination f - e
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h) h1
  · linarith
end Erdos654Proof
