-- Prove2me | solution 1 for Erdos180.symplecticAutomorphismLineEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T03:08:17.296833+00:00
-- url     : https://prove2.me/submissions/cc7a0eff-8ae0-45bf-900b-b53bce9d0eda

import Definitions.Def_erdos180_core4
import Mathlib.LinearAlgebra.Dimension.Finrank

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

@[simp]
theorem solution
    (e : SymplecticAutomorphism K)
    (L : SymplecticLine K) :
    symplecticAutomorphismLineEquiv K e L =
      symplecticAutomorphismLine K e L := by
  apply Subtype.ext
  rfl
