-- Prove2me | solution 1 for Erdos180.proposedFamilyFree_four_cycle
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:29:24.224329+00:00
-- url     : https://prove2.me/submissions/eb86bccf-14b7-4389-96fd-34a9367f5437

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Theorems.Thm_Erdos180_four_cycle_mem_proposedFamily

open Erdos180
open Finset SimpleGraph

theorem solution
    {n : ℕ} {host : SimpleGraph (Fin n)}
    (hfree : FamilyFree proposedFamily host) :
    (SimpleGraph.cycleGraph 4).Free host := by
  simpa [finiteCycle] using
    FamilyFree.member four_cycle_mem_proposedFamily hfree
