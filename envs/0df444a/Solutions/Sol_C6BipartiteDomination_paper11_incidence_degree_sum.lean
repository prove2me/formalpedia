-- Prove2me | solution 1 for C6BipartiteDomination.paper11_incidence_degree_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:56:59.55166+00:00
-- url     : https://prove2.me/submissions/b47d7085-8c7e-46df-b8ec-107843577011

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace C6BipartiteDomination
theorem _root_.solution
    (L R : Finset V) (E : Finset (V × V))
    (hE : E ⊆ L.product R) :
    (∑ w ∈ L, paper11LeftDegree E R w) = E.card ∧
      (∑ u ∈ R, paper11RightDegree E L u) = E.card := by
  classical
  constructor
  · have hmap : (E : Set (V × V)).MapsTo Prod.fst (L : Set V) := by
      intro e he
      have he' := hE he
      exact (Finset.mem_product.mp he').1
    have hcard := Finset.card_eq_sum_card_fiberwise (s := E) (t := L)
      (f := Prod.fst) hmap
    calc
      _ = ∑ w ∈ L, #{e ∈ E | e.1 = w} := by simp [paper11LeftDegree]
      _ = E.card := hcard.symm
  · have hmap : (E : Set (V × V)).MapsTo Prod.snd (R : Set V) := by
      intro e he
      have he' := hE he
      exact (Finset.mem_product.mp he').2
    have hcard := Finset.card_eq_sum_card_fiberwise (s := E) (t := R)
      (f := Prod.snd) hmap
    calc
      _ = ∑ u ∈ R, #{e ∈ E | e.2 = u} := by simp [paper11RightDegree]
      _ = E.card := hcard.symm
end C6BipartiteDomination
