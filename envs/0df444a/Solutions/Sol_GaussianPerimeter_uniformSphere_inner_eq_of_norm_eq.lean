-- Prove2me | solution 1 for GaussianPerimeter.uniformSphere_inner_eq_of_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:11:12.891897+00:00
-- url     : https://prove2.me/submissions/74a952b4-b197-4d6c-af1a-41db5a59138a

module
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Definitions.Def_GaussianPerimeter_Sphere
public import Theorems.Thm_GaussianPerimeter_uniformSphere_cap_isometric

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Function
open scoped ENNReal Pointwise RealInnerProductSpace
open GaussianPerimeter
local notation "UnitSphere" E => Metric.sphere (0 : E) 1
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] [Nontrivial F]
namespace GaussianPerimeter
theorem _root_.solution {x y : E} (hxy : ‖x‖ = ‖y‖) (c : ℝ) :
    uniformSphere E {u | ⟪x, (u : E)⟫ < c} =
    uniformSphere E {u | ⟪y, (u : E)⟫ < c} := by
  let R : E ≃ₗᵢ[ℝ] E := (ℝ ∙ (x - y))ᗮ.reflection
  have hR : R x = y := Submodule.reflection_sub hxy
  let S (x : E) : Set (UnitSphere E) := {u | c ≤ ⟪x, (u : E)⟫}
  have hs (x : E) : MeasurableSet (S x) :=
    measurableSet_le measurable_const (by fun_prop)
  have hS (x : E) : {u : UnitSphere E | ⟪x, (u : E)⟫ < c} = (S x)ᶜ := by
    ext u
    simp [S]
  rw [hS x, hS y, measure_compl (hs x) (measure_ne_top _ _),
    measure_compl (hs y) (measure_ne_top _ _)]
  congr 1
  simpa [S, hR] using uniformSphere_cap_isometric R x c
end GaussianPerimeter
