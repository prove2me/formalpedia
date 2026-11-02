-- Prove2me | solution 1 for FiniteEnergyPlane.isJHolomorphicOn_comp_of_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T10:32:10.852263+00:00
-- url     : https://prove2.me/submissions/03fff471-79d6-4137-8af2-2f6f584540ba

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

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem isJHolomorphicOn_comp_of_differentiableAt_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (U W : Set ℂ) (g : ℂ → E)
    (hg : JHolomorphic.IsJHolomorphicOn J U g)
    (hJ : ∀ z ∈ U, (J (g z)).comp (J (g z)) = -ContinuousLinearMap.id ℝ E) (f : ℂ → ℂ)
    (hf : ∀ z ∈ W, DifferentiableAt ℂ f z ∧ f z ∈ U) :
    JHolomorphic.IsJHolomorphicOn J W (fun z => g (f z)) := by
  intro z hz
  obtain ⟨hfd, hfU⟩ := hf z hz
  obtain ⟨hgd, hdb⟩ := hg (f z) hfU
  have hfc : HasDerivAt f (deriv f z) z := hfd.hasDerivAt
  refine ⟨hgd.comp z (hfd.restrictScalars ℝ), ?_⟩
  set c := deriv f z
  have hab : fderiv ℝ g (f z) 1 + J (g (f z)) (fderiv ℝ g (f z) Complex.I) = 0 := hdb
  have hJJ : ∀ v, J (g (f z)) (J (g (f z)) v) = -v := fun v => by
    have := congrArg (fun L : E →L[ℝ] E => L v) (hJ (f z) hfU)
    simpa using this
  have hJb : J (g (f z)) (fderiv ℝ g (f z) Complex.I) = -fderiv ℝ g (f z) 1 :=
    eq_neg_of_add_eq_zero_right hab
  have hJa : J (g (f z)) (fderiv ℝ g (f z) 1) = fderiv ℝ g (f z) Complex.I := by
    rw [← neg_neg (fderiv ℝ g (f z) 1), ← hJb, map_neg, hJJ, neg_neg]
  unfold JHolomorphic.dbarJ
  rw [pae_fderiv_comp_apply g f z c hfc hgd, pae_fderiv_comp_apply g f z c hfc hgd, mul_one]
  have hcI : fderiv ℝ g (f z) (c * Complex.I) =
      (-c.im) • fderiv ℝ g (f z) 1 + c.re • fderiv ℝ g (f z) Complex.I := by
    rw [pae_complex_decomp_I, map_add, map_smul, map_smul]
  rw [hcI]
  have hc : fderiv ℝ g (f z) c =
      c.re • fderiv ℝ g (f z) 1 + c.im • fderiv ℝ g (f z) Complex.I := by
    conv_lhs => rw [pae_complex_decomp c]
    simp only [map_add, map_smul]
  rw [hc]
  rw [map_add, map_smul, map_smul, hJa, hJb, smul_neg, neg_smul]
  abel

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (U W : Set ℂ) (g : ℂ → E)
    (hg : JHolomorphic.IsJHolomorphicOn J U g)
    (hJ : ∀ z ∈ U, (J (g z)).comp (J (g z)) = -ContinuousLinearMap.id ℝ E) (f : ℂ → ℂ)
    (hf : ∀ z ∈ W, DifferentiableAt ℂ f z ∧ f z ∈ U) :
    JHolomorphic.IsJHolomorphicOn J W (fun z => g (f z)) :=
  isJHolomorphicOn_comp_of_differentiableAt_aux J U W g hg hJ f hf
