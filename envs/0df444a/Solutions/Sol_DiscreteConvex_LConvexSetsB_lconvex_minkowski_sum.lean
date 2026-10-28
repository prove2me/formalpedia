-- Prove2me | solution 1 for DiscreteConvex.LConvexSetsB.lconvex_minkowski_sum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:06:32.492372+00:00
-- url     : https://prove2.me/submissions/218313e1-3408-4927-8150-2467492bdd29

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexSetsB_LConvexSet
import Definitions.Def_DiscreteConvex_LConvexSetsB_IntEmbed
open scoped Pointwise
open DiscreteConvex.LConvexSetsB

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (D1 D2 : Set (V → ℤ))
    (hD1 : LConvexSet D1) (hD2 : LConvexSet D2) :
    convexHull ℝ (IntEmbed (D1 + D2)) = convexHull ℝ (IntEmbed D1) + convexHull ℝ (IntEmbed D2) := by
  have h : IntEmbed (D1 + D2) = IntEmbed D1 + IntEmbed D2 := by
    unfold IntEmbed
    let f : (V → ℤ) →+ (V → ℝ) :=
      { toFun := fun x v => (x v : ℝ), map_zero' := by ext; simp,
        map_add' := by intro x y; ext; simp }
    exact Set.image_add f
  rw [h, convexHull_add]
