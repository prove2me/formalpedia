-- Prove2me | solution 1 for FiniteEnergyPlane.ds_dt_comp_of_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T10:27:50.838023+00:00
-- url     : https://prove2.me/submissions/7187ee1b-0904-43a6-9031-ad5ed2d54ddb

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem pae_fderiv_comp_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : ℂ → F) (f : ℂ → ℂ) (z c : ℂ) (hf : HasDerivAt f c z)
    (hg : DifferentiableAt ℝ g (f z)) (v : ℂ) :
    fderiv ℝ (fun w => g (f w)) z v = fderiv ℝ g (f z) (c * v) := by
  have hfR : HasFDerivAt f ((ContinuousLinearMap.toSpanSingleton ℂ c).restrictScalars ℝ) z :=
    HasFDerivAt.restrictScalars ℝ hf.hasFDerivAt
  have := (hg.hasFDerivAt.comp z hfR).fderiv
  rw [show (fun w => g (f w)) = g ∘ f from rfl, this]
  simp [mul_comm]

theorem pae_complex_decomp (c : ℂ) : c = (c.re : ℝ) • (1 : ℂ) + (c.im : ℝ) • Complex.I := by
  apply Complex.ext <;> simp

theorem pae_complex_decomp_I (c : ℂ) :
    c * Complex.I = (-c.im : ℝ) • (1 : ℂ) + (c.re : ℝ) • Complex.I := by
  apply Complex.ext <;> simp

theorem ds_dt_comp_of_hasDerivAt_aux {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : ℂ → F) (f : ℂ → ℂ) (z c : ℂ) (hf : HasDerivAt f c z)
    (hg : DifferentiableAt ℝ g (f z)) :
    ds (fun w => g (f w)) z = c.re • ds g (f z) + c.im • dt g (f z) ∧
      dt (fun w => g (f w)) z = -c.im • ds g (f z) + c.re • dt g (f z) := by
  constructor
  · simp only [ds, dt]
    rw [pae_fderiv_comp_apply g f z c hf hg, mul_one]
    conv_lhs => rw [pae_complex_decomp c]
    rw [map_add, map_smul, map_smul]
  · simp only [ds, dt]
    rw [pae_fderiv_comp_apply g f z c hf hg, pae_complex_decomp_I, map_add, map_smul, map_smul]

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : ℂ → F) (f : ℂ → ℂ) (z c : ℂ) (hf : HasDerivAt f c z)
    (hg : DifferentiableAt ℝ g (f z)) :
    ds (fun w => g (f w)) z = c.re • ds g (f z) + c.im • dt g (f z) ∧
      dt (fun w => g (f w)) z = -c.im • ds g (f z) + c.re • dt g (f z) :=
  ds_dt_comp_of_hasDerivAt_aux g f z c hf hg
