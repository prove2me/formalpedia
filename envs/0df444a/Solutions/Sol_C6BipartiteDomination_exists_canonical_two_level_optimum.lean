-- Prove2me | solution 1 for C6BipartiteDomination.exists_canonical_two_level_optimum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:50:02.533513+00:00
-- url     : https://prove2.me/submissions/6fe9abdc-188d-4e3a-a7ab-ef05206bb3d5

import Definitions.Def_C6BipartiteDomination_A3
import Definitions.Def_C6BipartiteDomination_A4
import Theorems.Thm_C6BipartiteDomination_exists_maximal_independent_subset


set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution :
    ∃ D : Finset V, CanonicalTwoLevelOptimum G D := by
  classical
  obtain ⟨I, hIall, hIind, hImax⟩ := exists_maximal_independent_subset G Finset.univ
  have hIdom : Dominates G I := by
    intro v hv
    have hvAll : v ∈ (Finset.univ : Finset V) := Finset.mem_univ _
    exact hImax hvAll hv
  have hIbip : IsBipartiteOn G I := by
    refine ⟨fun _ => false, ?_⟩
    intro u v hu hv hadj
    exact (hIind hu hv hadj).elim
  let feasible := Finset.univ.powerset.filter (IsBipartiteDominatingSet G)
  have hIfeas : I ∈ feasible := by
    simp only [feasible, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.subset_univ I, ⟨hIdom, hIbip⟩⟩
  obtain ⟨D₀, hD₀mem, hD₀min⟩ :=
    Finset.exists_min_image feasible Finset.card ⟨I, hIfeas⟩
  let cooptimal := feasible.filter fun E => E.card = D₀.card
  have hD₀co : D₀ ∈ cooptimal := by
    simp [cooptimal, hD₀mem]
  obtain ⟨D, hDmem, hDarcmin⟩ :=
    Finset.exists_min_image cooptimal (fun E => (internalArcs G E).card) ⟨D₀, hD₀co⟩
  have hDfeas : D ∈ feasible := (Finset.mem_filter.mp hDmem).1
  have hDprop : IsBipartiteDominatingSet G D := (Finset.mem_filter.mp hDfeas).2
  have hDcard : D.card = D₀.card := (Finset.mem_filter.mp hDmem).2
  refine ⟨D, hDprop, ?_, ?_⟩
  · intro E hE
    have hEmem : E ∈ feasible := by simp [feasible, hE]
    rw [hDcard]
    exact hD₀min E hEmem
  · intro E hE hEq
    have hEmem : E ∈ feasible := by simp [feasible, hE]
    have hEco : E ∈ cooptimal := by
      simp [cooptimal, hEmem, hEq, (Finset.mem_filter.mp hDmem).2]
    exact hDarcmin E hEco
end C6BipartiteDomination
