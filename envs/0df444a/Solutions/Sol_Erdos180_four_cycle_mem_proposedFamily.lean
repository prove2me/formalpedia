-- Prove2me | solution 1 for Erdos180.four_cycle_mem_proposedFamily
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:27:40.63291+00:00
-- url     : https://prove2.me/submissions/ee37d28d-1c3c-473e-9baa-ca5097c2fe17

import Definitions.Def_erdos180_core4
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Data.Fintype.Sum
import Theorems.Thm_Erdos180_proposedFamily_mem_iff

open Erdos180
open Finset SimpleGraph

theorem solution :
    finiteCycle 4 ∈ proposedFamily :=
  proposedFamily_mem_iff.mpr (.inl (.inl (.inl rfl)))
