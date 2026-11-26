-- Prove2me | solution 1 for Erdos1007.unitDistance_comap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:53:45.413999+00:00
-- url     : https://prove2.me/submissions/fc87dc8f-d62c-45c8-939f-c3e2193c092a

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Definitions.Def_Erdos1007_Geometry_UnitDistanceComap

set_option autoImplicit false
@[expose] public section
open Erdos1007
open SimpleGraph
public section
namespace Erdos1007
theorem _root_.solution {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {n : ℕ}
    (φ : H →g G) (hφ : Function.Injective φ) :
    (∃ f : V → EuclideanSpace ℝ (Fin n), Function.Injective f ∧
        ∀ u v, G.Adj u v → dist (f u) (f v) = 1) →
      ∃ g : W → EuclideanSpace ℝ (Fin n), Function.Injective g ∧
        ∀ u v, H.Adj u v → dist (g u) (g v) = 1 := by
  rintro ⟨f, hfInj, hfDist⟩
  refine ⟨fun w => f (φ w), hfInj.comp hφ, ?_⟩
  intro u v huv
  exact hfDist (φ u) (φ v) (φ.map_adj huv)
end Erdos1007
