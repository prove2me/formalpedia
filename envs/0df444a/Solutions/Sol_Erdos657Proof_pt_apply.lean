-- Prove2me | solution 1 for Erdos657Proof.pt_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:22:06.753796+00:00
-- url     : https://prove2.me/submissions/2c16b531-cc71-471b-a94c-8f366019880b

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
theorem _root_.solution {k : ℕ} (S : Finset (Fin k)) (i : Fin k) : pt S i = if i ∈ S then w i else 0 :=
  rfl
end Erdos657Proof
