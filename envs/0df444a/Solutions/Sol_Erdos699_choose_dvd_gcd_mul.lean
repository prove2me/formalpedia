-- Prove2me | solution 1 for Erdos699.choose_dvd_gcd_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:48:44.332746+00:00
-- url     : https://prove2.me/submissions/044dfddf-028a-422d-b69e-cd0edc572acf

module
public import Mathlib
public import Definitions.Def_Erdos699_Basic

set_option autoImplicit false
@[expose] public section
public section
open Erdos699
namespace Erdos699
theorem _root_.solution {n i j : ℕ} (hij : i ≤ j) :
    n.choose i ∣ Nat.gcd (n.choose i) (n.choose j) * j.choose i := by
  rw [← Nat.gcd_mul_right]
  refine Nat.dvd_gcd (Nat.dvd_mul_right _ _) ?_
  rw [Nat.choose_mul (n := n) hij]
  exact Nat.dvd_mul_right _ _
end Erdos699
