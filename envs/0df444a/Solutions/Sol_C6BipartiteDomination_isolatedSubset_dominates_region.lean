-- Prove2me | solution 1 for C6BipartiteDomination.isolatedSubset_dominates_region
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:42:20.825798+00:00
-- url     : https://prove2.me/submissions/03e9f206-894c-4723-b2fa-b10cfa55229b

import Definitions.Def_C6BipartiteDomination_Basic
import Definitions.Def_C6BipartiteDomination_A2
import Theorems.Thm_C6BipartiteDomination_mem_responsibilityRegion
import Theorems.Thm_C6BipartiteDomination_isolatedSubset_region_subset

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D X : Finset V} (hD : IsBipartiteDominatingSet G D)
    (hX : IsolatedSubset G D X) : BipartiteDominatingOn G (responsibilityRegion G D X) X := by
  classical
  refine ⟨isolatedSubset_region_subset G hX, ?_, ?_⟩
  · intro v hvR hvX
    have hvD : v ∉ D := by
      intro hvD
      have hvRet : v ∈ D \ X := Finset.mem_sdiff.mpr ⟨hvD, by
        intro hvX'
        exact hvX hvX'
      ⟩
      exact (mem_responsibilityRegion G D X v).mp hvR |>.1 hvRet
    obtain ⟨u, huD, huAdj⟩ := hD.1 hvD
    have huNotRet : u ∉ D \ X := by
      intro huRet
      exact ((mem_responsibilityRegion G D X v).mp hvR).2 u huRet huAdj
    have huX : u ∈ X := by
      by_contra h
      exact huNotRet (Finset.mem_sdiff.mpr ⟨huD, h⟩)
    exact ⟨u, huX, huAdj⟩
  · refine ⟨fun _ => false, ?_⟩
    intro x y hx hy hxy
    exact (hX.2 hx (hX.1 hy) hxy).elim
end C6BipartiteDomination
