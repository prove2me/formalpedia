-- Prove2me | solution 1 for Erdos835Palomar.johnsonGraph_18_9_chromaticNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:39:39.954646+00:00
-- url     : https://prove2.me/submissions/d9e1d201-d0ab-40b7-9021-7c607c31a155

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib
public import Definitions.Def_Erdos835Palomar_Solution
public import Theorems.Thm_Erdos835Palomar_johnson_chromaticNumber_composite

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open Erdos835Palomar
variable {α : Type*} [DecidableEq α]
variable {k : ℕ}
namespace Erdos835Palomar
theorem _root_.solution : J(18, 9).chromaticNumber > 9 + 1 :=
  johnson_chromaticNumber_composite 9 (by norm_num) ⟨by norm_num, by norm_num⟩
end Erdos835Palomar
