-- Prove2me | solution 1 for Erdos835Palomar.not_property_of_not_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:28:11.970167+00:00
-- url     : https://prove2.me/submissions/d2466615-1b39-4b28-bb19-d5714906c722

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib
public import Definitions.Def_Erdos835Palomar_Solution
public import Theorems.Thm_Erdos835Palomar_not_dvd_choose
public import Theorems.Thm_Erdos835Palomar_color_count

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open Erdos835Palomar
variable {α : Type*} [DecidableEq α]
variable {k : ℕ}
namespace Erdos835Palomar
theorem _root_.solution (k : ℕ) (hk : 2 ≤ k) (hnp : ¬ (k + 1).Prime) :
    ¬ Property k := by
  rintro ⟨c, hc⟩
  set p := (k + 1).minFac
  have hpr : p.Prime := Nat.minFac_prime (by omega)
  have hlt : p < k + 1 := (Nat.not_prime_iff_minFac_lt (by omega)).mp hnp
  obtain ⟨W, -, hW⟩ := exists_subset_card_eq (s := (univ : Finset (Fin (2 * k)))) (n := k + p)
    (by rw [card_univ, Fintype.card_fin]; omega)
  have h := color_count c hc 0 p hpr.one_lt.le W hW
  exact not_dvd_choose k p hpr (Nat.minFac_dvd _) hlt ⟨_, h.symm⟩
end Erdos835Palomar
