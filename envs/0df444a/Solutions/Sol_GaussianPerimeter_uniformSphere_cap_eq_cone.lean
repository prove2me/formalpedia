-- Prove2me | solution 1 for GaussianPerimeter.uniformSphere_cap_eq_cone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:10:43.42431+00:00
-- url     : https://prove2.me/submissions/8b925e18-7a1d-48db-8120-3154d0636072

module
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Definitions.Def_GaussianPerimeter_Sphere

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Function
open scoped ENNReal Pointwise RealInnerProductSpace
open GaussianPerimeter
local notation "UnitSphere" E => Metric.sphere (0 : E) 1
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace GaussianPerimeter
theorem _root_.solution [Nontrivial E] (v : E) (t : ℝ) :
    uniformSphere E {u | t ≤ ⟪v, (u : E)⟫} =
      volume (capCone v t) / volume (Metric.ball (0 : E) 1) := by
  let μ : Measure E := volume
  let s : Set (UnitSphere E) := {u | t ≤ ⟪v, (u : E)⟫}
  have hs : MeasurableSet s := measurableSet_le measurable_const (by fun_prop)
  have hcone : Ioo (0 : ℝ) 1 • (Subtype.val '' s) = capCone v t := by
    ext u
    constructor
    · rintro ⟨r, hr, _, ⟨w, hw, rfl⟩, rfl⟩
      have hwn : ‖(w : E)‖ = 1 := by
        rw [← dist_zero_right]
        exact w.property
      simp only [capCone, mem_ofPred_eq, norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, hwn, mul_one,
        real_inner_smul_right]
      exact ⟨hr.1, hr.2, by simpa [mul_comm] using mul_le_mul_of_nonneg_left hw hr.1.le⟩
    · rintro ⟨hu, hu₁, hvu⟩
      let w : E := ‖u‖⁻¹ • u
      have hwn : ‖w‖ = 1 := by
        simp [w, norm_smul, hu.ne']
      have hw : w ∈ Metric.sphere (0 : E) 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hwn
      refine ⟨‖u‖, ⟨hu, hu₁⟩, w, ⟨⟨w, hw⟩, ?_, rfl⟩, ?_⟩
      · change t ≤ ⟪v, w⟫
        rw [show w = ‖u‖⁻¹ • u from rfl, real_inner_smul_right]
        exact (le_inv_mul_iff₀ hu).2 (by simpa [mul_comm] using hvu)
      · simp [w, smul_smul, hu.ne']
  change uniformSphere E s = _
  rw [uniformSphere, Measure.smul_apply, smul_eq_mul, Measure.toSphere_apply_univ,
    Measure.toSphere_apply' _ hs, hcone]
  have hf : (↑(Module.finrank ℝ E) : ℝ≥0∞) ≠ 0 := by
    have hd : 0 < Module.finrank ℝ E := Module.finrank_pos
    exact_mod_cast hd.ne'
  have hft : (↑(Module.finrank ℝ E) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  rw [ENNReal.mul_inv (Or.inl hf) (Or.inl hft), div_eq_mul_inv]
  calc
    _ = ((↑(Module.finrank ℝ E) : ℝ≥0∞)⁻¹ * ↑(Module.finrank ℝ E)) *
        (μ (capCone v t) * (μ (Metric.ball 0 1))⁻¹) := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel hf hft, one_mul]
end GaussianPerimeter
