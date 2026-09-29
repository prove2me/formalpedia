-- Prove2me | solution 1 for Erdos180.jQuotient_mem_proposedFamily
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:31:08.421288+00:00
-- url     : https://prove2.me/submissions/d05a5013-535a-4277-a929-8bae2841f307

import Definitions.Def_erdos180_core4
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Data.Fintype.Sum
import Theorems.Thm_Erdos180_proposedFamily_mem_iff

open Erdos180
open Finset SimpleGraph

theorem solution
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    encodeFiniteGraph (quotientGraph jTemplate f) ∈ proposedFamily :=
  proposedFamily_mem_iff.mpr (.inl (.inr ⟨f, hf, rfl⟩))
