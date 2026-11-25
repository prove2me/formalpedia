-- Prove2me | solution 1 for CliqueMinors.three_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:33:52.391796+00:00
-- url     : https://prove2.me/submissions/ddaff9f9-ab90-40c2-a487-0d08e95bd131

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V : Type*}
open scoped Classical
variable [Fintype V]
omit [Fintype V]
namespace CliqueMinors
theorem _root_.solution {s : Finset V} {p q r : V} (hp : p ∈ s) (hq : q ∈ s) (hr : r ∈ s)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) : 3 ≤ s.card := by
  have h3 : ({p, q, r} : Finset V).card = 3 := Finset.card_eq_three.2 ⟨p, q, r, hpq, hpr, hqr, rfl⟩
  rw [← h3]
  refine Finset.card_le_card fun t ht => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl <;> assumption
end CliqueMinors
