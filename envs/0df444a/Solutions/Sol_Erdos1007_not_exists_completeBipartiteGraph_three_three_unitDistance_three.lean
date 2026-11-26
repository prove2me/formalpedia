-- Prove2me | solution 1 for Erdos1007.not_exists_completeBipartiteGraph_three_three_unitDistance_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:56:08.208822+00:00
-- url     : https://prove2.me/submissions/681db980-504a-46cd-9223-20a8bbafaa39

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Algebra.Torsor.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Geometry.Euclidean.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_Erdos1007_Geometry_CompleteBipartiteLowerBound
public import Theorems.Thm_Erdos1007_not_forall_dist_eq_one_of_injective_fin_three

set_option autoImplicit false
@[expose] public section
open Erdos1007
open Module Submodule AffineSubspace EuclideanGeometry
open scoped RealInnerProductSpace
public section
namespace Erdos1007
theorem _root_.solution :
    ¬ ∃ f : Fin 3 ⊕ Fin 3 → EuclideanSpace ℝ (Fin 3), Function.Injective f ∧
      ∀ u v, (completeBipartiteGraph (Fin 3) (Fin 3)).Adj u v → dist (f u) (f v) = 1 := by
  rintro ⟨f, hf, hadj⟩
  refine not_forall_dist_eq_one_of_injective_fin_three (f ∘ Sum.inl) (f ∘ Sum.inr)
      (hf.comp Sum.inl_injective) (hf.comp Sum.inr_injective) ?_
  intro i j
  exact hadj (Sum.inl i) (Sum.inr j) (by simp [completeBipartiteGraph_adj])
end Erdos1007
