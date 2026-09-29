-- Prove2me | solution 1 for Erdos180.symplecticLineGraphMap_horizontal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T03:10:52.592463+00:00
-- url     : https://prove2.me/submissions/44a7b305-a80b-4dcf-b45a-82ddd1ca1459

import Definitions.Def_erdos180_core4
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Finrank

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem solution
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1)
    (x : L.1) :
    symplecticLineGraphMap K L hvertical
        (symplecticHorizontalProjection K
          (x : SymplecticVector K)) =
      symplecticVerticalProjection K
        (x : SymplecticVector K) := by
  change
    symplecticVerticalProjection K
      ((symplecticLineHorizontalProjectionEquiv K L hvertical).symm
        (symplecticLineHorizontalProjectionEquiv K L hvertical x) :
          SymplecticVector K) = _
  rw [LinearEquiv.symm_apply_apply]
