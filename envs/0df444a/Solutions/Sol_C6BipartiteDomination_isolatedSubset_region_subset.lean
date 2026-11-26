-- Prove2me | solution 1 for C6BipartiteDomination.isolatedSubset_region_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:41:36.421368+00:00
-- url     : https://prove2.me/submissions/a8329573-0c2e-4e14-85c3-a03be8eb1f60

import Definitions.Def_C6BipartiteDomination_Basic
import Definitions.Def_C6BipartiteDomination_A2
import Theorems.Thm_C6BipartiteDomination_mem_responsibilityRegion

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D X : Finset V} (hX : IsolatedSubset G D X) :
    X ⊆ responsibilityRegion G D X := by
  classical
  intro x hx
  rw [mem_responsibilityRegion]
  refine ⟨?_, ?_⟩
  · intro hxret
    exact (Finset.mem_sdiff.mp hxret).2 hx
  · intro u hu hAdj
    exact hX.2 hx (Finset.mem_sdiff.mp hu).1 (hAdj.symm)
end C6BipartiteDomination
