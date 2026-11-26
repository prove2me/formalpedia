-- Prove2me | solution 1 for Erdos1007.unitDistance_of_embedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:54:17.888737+00:00
-- url     : https://prove2.me/submissions/85f671a4-a1a2-4cd1-85d3-890f6bea0023

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
theorem _root_.solution {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {n : ℕ}
    (φ : H ↪g G) :
    (∃ f : V → EuclideanSpace ℝ (Fin n), Function.Injective f ∧
        ∀ u v, G.Adj u v → dist (f u) (f v) = 1) →
      ∃ g : W → EuclideanSpace ℝ (Fin n), Function.Injective g ∧
        ∀ u v, H.Adj u v → dist (g u) (g v) = 1 :=
  unitDistance_comap φ.toHom φ.injective
end Erdos1007
