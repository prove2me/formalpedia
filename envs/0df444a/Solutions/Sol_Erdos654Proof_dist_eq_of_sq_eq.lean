-- Prove2me | solution 1 for Erdos654Proof.dist_eq_of_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:47:48.088397+00:00
-- url     : https://prove2.me/submissions/d9e5dc76-8d15-4ea0-9010-4efa65f93fe0

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
theorem _root_.solution {P Q P' Q' : ℝ²} (h : dist P Q ^ 2 = dist P' Q' ^ 2) :
    dist P Q = dist P' Q' :=
  (pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).1 h
end Erdos654Proof
