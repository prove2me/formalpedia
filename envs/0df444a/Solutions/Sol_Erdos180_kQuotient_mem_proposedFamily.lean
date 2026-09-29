-- Prove2me | solution 1 for Erdos180.kQuotient_mem_proposedFamily
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:32:00.257914+00:00
-- url     : https://prove2.me/submissions/698f9b5f-3a7d-4722-8d0a-27a7d43e7c60

import Definitions.Def_erdos180_core4
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Data.Fintype.Sum
import Theorems.Thm_Erdos180_proposedFamily_mem_iff

open Erdos180
open Finset SimpleGraph

theorem solution
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    encodeFiniteGraph (quotientGraph kTemplate f) ∈ proposedFamily :=
  proposedFamily_mem_iff.mpr (.inr ⟨f, hf, rfl⟩)
