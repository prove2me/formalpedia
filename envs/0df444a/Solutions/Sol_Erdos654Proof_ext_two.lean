-- Prove2me | solution 1 for Erdos654Proof.ext_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:38:12.626254+00:00
-- url     : https://prove2.me/submissions/77223800-a738-47fb-83b4-88b34801ec03

module
public import Mathlib
public import Definitions.Def_Erdos654Palomar_Solution

set_option autoImplicit true
@[expose] public section
public section
open scoped EuclideanGeometry Finset
open Filter Finset EuclideanGeometry
open Erdos654Proof
namespace Erdos654Proof
theorem _root_.solution {P Q : ℝ²} (h0 : P 0 = Q 0) (h1 : P 1 = Q 1) : P = Q :=
  PiLp.ext (Fin.forall_fin_two.2 ⟨h0, h1⟩)
end Erdos654Proof
