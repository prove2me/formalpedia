-- Prove2me | solution 1 for GaussianPerimeter.mem_strictFacet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:05:59.945736+00:00
-- url     : https://prove2.me/submissions/094e8620-3182-4085-8fd7-55ca31a30ff3

module
public import Definitions.Def_GaussianPerimeter_Definitions
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Definitions.Def_GaussianPerimeter_Geometry

set_option autoImplicit true
@[expose] public section
public section
open Function Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal InnerProductSpace RealInnerProductSpace Function
open GaussianPerimeter
local notation "Euc" k => EuclideanSpace ℝ (Fin k)
variable {k : ℕ} {ι : Type*}
namespace GaussianPerimeter
theorem _root_.solution (u : ι → Euc (k + 1)) (ρ : ℝ) (i : ι) (x : Euc (k + 1)) :
    x ∈ strictFacet u ρ i ↔
      ⟪u i, x⟫_ℝ = ρ ∧ ∀ j ≠ i, ⟪u j, x⟫_ℝ < ρ := by
  simp [strictFacet, Subtype.forall]
end GaussianPerimeter
