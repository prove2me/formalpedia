-- Prove2me | solution 1 for Erdos1007.unitDistance_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:54:21.048826+00:00
-- url     : https://prove2.me/submissions/9ce5b402-46ed-470e-9ba0-988f75797b3f

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Definitions.Def_Erdos1007_Geometry_UnitDistanceComap
public import Theorems.Thm_Erdos1007_unitDistance_comap

set_option autoImplicit false
@[expose] public section
open Erdos1007
open SimpleGraph
public section
namespace Erdos1007
theorem _root_.solution {V : Type*} {G H : SimpleGraph V} {n : ℕ} (hHG : H ≤ G) :
    (∃ f : V → EuclideanSpace ℝ (Fin n), Function.Injective f ∧
        ∀ u v, G.Adj u v → dist (f u) (f v) = 1) →
      ∃ g : V → EuclideanSpace ℝ (Fin n), Function.Injective g ∧
        ∀ u v, H.Adj u v → dist (g u) (g v) = 1 :=
  unitDistance_comap (Hom.ofLE hHG) Function.injective_id
end Erdos1007
