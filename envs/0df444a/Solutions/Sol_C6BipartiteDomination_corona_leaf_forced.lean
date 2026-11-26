-- Prove2me | solution 1 for C6BipartiteDomination.corona_leaf_forced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:10:04.160963+00:00
-- url     : https://prove2.me/submissions/c3f327f4-21e4-4509-aacc-7e3256f676a7

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset CoronaVertex}
    (hD : IsBipartiteDominatingSet coronaGraph D)
    {i : Fin 5} (hi : i ∉ coronaSelectedCore D) (p : Fin 2) :
    Sum.inr (i, p) ∈ D := by
  classical
  have hiCore : Sum.inl i ∉ D := by
    intro h
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  by_contra hleaf
  obtain ⟨y, hyD, hyAdj⟩ := hD.1 hleaf
  cases y with
  | inl j =>
      have hji : j = i := by
        simpa [coronaGraph, coronaAdj] using hyAdj
      subst j
      exact hiCore hyD
  | inr q =>
      simp [coronaGraph, coronaAdj] at hyAdj
end C6BipartiteDomination
