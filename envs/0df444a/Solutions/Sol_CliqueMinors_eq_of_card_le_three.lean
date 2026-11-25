-- Prove2me | solution 1 for CliqueMinors.eq_of_card_le_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:33:54.748546+00:00
-- url     : https://prove2.me/submissions/ecf6223a-c504-44fd-a306-556091d51127

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
theorem _root_.solution {s : Finset V} (h : s.card ≤ 3) {p q r : V} (hp : p ∈ s)
    (hq : q ∈ s) (hr : r ∈ s) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) {t : V} (ht : t ∈ s) :
    t = p ∨ t = q ∨ t = r := by
  by_contra hne
  simp only [not_or] at hne
  have h3 : ({p, q, r} : Finset V).card = 3 := Finset.card_eq_three.2 ⟨p, q, r, hpq, hpr, hqr, rfl⟩
  have h4 : (insert t ({p, q, r} : Finset V)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hne.1, hne.2.1, hne.2.2]), h3]
  have : (insert t ({p, q, r} : Finset V)).card ≤ s.card := by
    refine Finset.card_le_card fun u hu => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> assumption
  omega
end CliqueMinors
