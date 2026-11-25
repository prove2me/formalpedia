-- Prove2me | solution 1 for Erdos835Palomar.johnson_chromaticNumber_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:39:37.201646+00:00
-- url     : https://prove2.me/submissions/7d1f962d-34e1-461f-858e-91efae2004cb

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
theorem _root_.solution (k : ℕ) (hk : 2 < k) (h : Odd k) :
    k + 1 < J(2 * k, k).chromaticNumber := by
  refine johnson_chromaticNumber_composite k hk ⟨by omega, ?_⟩
  rw [Nat.not_prime_iff_exists_dvd_lt (by omega)]
  use 2
  constructor
  · exact even_iff_two_dvd.mp (Odd.add_one h)
  · omega
end Erdos835Palomar
