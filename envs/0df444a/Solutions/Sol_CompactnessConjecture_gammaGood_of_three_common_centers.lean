-- Prove2me | solution 1 for CompactnessConjecture.gammaGood_of_three_common_centers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/85680786-b833-4ab9-8f54-6d590da9bb4d

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace CompactnessConjecture
theorem _root_.solution
    {G : SimpleGraph V}
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (base : Fin 3 → V)
    (hbase : Function.Injective base)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    {u : V}
    (hu : u ∈ tripleCommonCenters G base)
    (hcenters : 3 ≤ (tripleCommonCenters G base).card) :
    GammaGood G u := by
  classical
  have herase :
      1 < ((tripleCommonCenters G base).erase u).card := by
    rw [Finset.card_erase_of_mem hu]
    omega
  obtain ⟨first, hfirst, second, hsecond, hdistinct⟩ :=
    Finset.one_lt_card.mp herase
  have hfirstne : first ≠ u := (Finset.mem_erase.mp hfirst).1
  have hsecondne : second ≠ u := (Finset.mem_erase.mp hsecond).1
  have hfirstmem : first ∈ tripleCommonCenters G base :=
    (Finset.mem_erase.mp hfirst).2
  have hsecondmem : second ∈ tripleCommonCenters G base :=
    (Finset.mem_erase.mp hsecond).2
  let center : Fin 3 → V := ![u, first, second]
  have hcenter : Function.Injective center := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [center]
  have hrelated : ∀ i j,
      CommonNeighborRelated G (base i) (center j) := by
    intro i j
    fin_cases j
    · exact (mem_tripleCommonCenters G base u).mp hu i
    · exact (mem_tripleCommonCenters G base first).mp hfirstmem i
    · exact (mem_tripleCommonCenters G base second).mp hsecondmem i
  let witness := subdivisionCopyOfGirthEightCenters
    hbip hfour hsix base center hbase hcenter hbase_unrelated hrelated
  refine ⟨witness, ?_⟩
  rfl
end CompactnessConjecture
