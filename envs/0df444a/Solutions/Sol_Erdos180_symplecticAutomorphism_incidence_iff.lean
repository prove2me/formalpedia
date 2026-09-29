-- Prove2me | solution 1 for Erdos180.symplecticAutomorphism_incidence_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T03:07:35.853042+00:00
-- url     : https://prove2.me/submissions/8218f94c-815f-471f-8c59-8e76d32989e4

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
import Mathlib.LinearAlgebra.Dimension.Finrank

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem solution
    (e : SymplecticAutomorphism K)
    (p : SymplecticPoint K) (L : SymplecticLine K) :
    (symplecticAutomorphismPoint K e p).1 ≤
        (symplecticAutomorphismLine K e L).1 ↔
      p.1 ≤ L.1 := by
  change
    p.1.map e.toLinearEquiv.toLinearMap ≤
      L.1.map e.toLinearEquiv.toLinearMap ↔ p.1 ≤ L.1
  exact LinearMap.map_le_map_iff'
    (LinearMap.ker_eq_bot.mpr e.toLinearEquiv.injective)
