-- Prove2me | solution 1 for GaussianPerimeter.uniformSphere_cap_isometric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:12:15.345804+00:00
-- url     : https://prove2.me/submissions/918b4cf1-afa3-4a00-a903-a54dc7a2d810

module
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Definitions.Def_GaussianPerimeter_Sphere
public import Theorems.Thm_GaussianPerimeter_measurableSet_capCone
public import Theorems.Thm_GaussianPerimeter_uniformSphere_cap_eq_cone

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
theorem _root_.solution (e : E ≃ₗᵢ[ℝ] F) (x : E) (c : ℝ) :
    uniformSphere E {u | c ≤ ⟪x, (u : E)⟫} =
      uniformSphere F {u | c ≤ ⟪e x, (u : F)⟫} := by
  rw [uniformSphere_cap_eq_cone, uniformSphere_cap_eq_cone,
    ← e.measurePreserving.measure_preimage (measurableSet_capCone (e x) c).nullMeasurableSet,
    ← e.measurePreserving.measure_preimage measurableSet_ball.nullMeasurableSet]
  have hcone : e ⁻¹' capCone (e x) c = capCone x c := by
    ext z
    simp [capCone, LinearIsometryEquiv.inner_map_map]
  have hball : e ⁻¹' Metric.ball (0 : F) 1 = Metric.ball (0 : E) 1 := by
    ext z
    simp [Metric.mem_ball, dist_zero_right]
  rw [hcone, hball]
end GaussianPerimeter
