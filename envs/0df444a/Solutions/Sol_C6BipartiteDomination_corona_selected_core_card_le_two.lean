-- Prove2me | solution 1 for C6BipartiteDomination.corona_selected_core_card_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:09:39.762376+00:00
-- url     : https://prove2.me/submissions/9cce7652-5b16-4a61-a714-c95cf71243c3

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset CoronaVertex}
    (hD : IsBipartiteDominatingSet coronaGraph D) :
    (coronaSelectedCore D).card ≤ 2 := by
  classical
  obtain ⟨colour, hcolour⟩ := hD.2
  let C := coronaSelectedCore D
  let f : {i // i ∈ C} → Bool := fun i => colour (Sum.inl i.1)
  have hinj : Function.Injective f := by
    intro i j hEq
    by_contra hne
    have hiD : Sum.inl i.1 ∈ D := by
      simpa [C, coronaSelectedCore] using i.2
    have hjD : Sum.inl j.1 ∈ D := by
      simpa [C, coronaSelectedCore] using j.2
    have hij : i.1 ≠ j.1 := by
      intro h
      exact hne (Subtype.ext h)
    have hadj : coronaGraph.Adj (Sum.inl i.1) (Sum.inl j.1) := by
      simpa [coronaGraph, coronaAdj] using hij
    exact (hcolour hiD hjD hadj) hEq
  have hcard : Fintype.card {i // i ∈ C} ≤ Fintype.card Bool :=
    Fintype.card_le_of_injective f hinj
  have hcard' : Fintype.card {i // i ∈ C} ≤ 2 := by simpa using hcard
  have hsubCard : Fintype.card {i // i ∈ C} = C.card := by
    simpa using Finset.card_attach C
  rw [hsubCard] at hcard'
  exact hcard'
end C6BipartiteDomination
