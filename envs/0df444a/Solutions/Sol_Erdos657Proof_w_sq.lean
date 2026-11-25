-- Prove2me | solution 1 for Erdos657Proof.w_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:21:35.897502+00:00
-- url     : https://prove2.me/submissions/c7901b32-0778-42fe-b4f1-17e54de51aaf

module
public import Mathlib
public import Definitions.Def_Erdos657Palomar_Solution

set_option autoImplicit true
@[expose] public section
public section
open scoped Finset
open Filter
open scoped EuclideanGeometry
open Erdos657Proof
open Finset
namespace Erdos657Proof
theorem _root_.solution (i : ℕ) : w i ^ 2 = 2 ^ i := Real.sq_sqrt (by positivity)
end Erdos657Proof
