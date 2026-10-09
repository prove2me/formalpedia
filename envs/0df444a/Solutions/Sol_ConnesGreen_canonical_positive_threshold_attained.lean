-- Prove2me | solution 1 for ConnesGreen.canonical_positive_threshold_attained
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T06:01:30.381698+00:00
-- url     : https://prove2.me/submissions/8ffed80a-e0bd-4aa0-8d8c-e606797ccd8d

import Definitions.Def_ConnesGreen_selected_loss_covariance
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

import Theorems.Thm_ConnesGreen_canonicalPositiveCovariance_compact
import Theorems.Thm_ConnesGreen_canonical_positive_threshold_mem_real_spectrum
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ContinuousLinearMap Set Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open ConnesGreen WeilDefect WeilDefect.ConnesNative
open ContinuousFunctionalCalculus
namespace ConnesGreen
private instance physicalRealCFC (t : ℝ) :
    IsometricContinuousFunctionalCalculus ℝ (Physical t →L[ℂ] Physical t) IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus (A := Physical t →L[ℂ] Physical t)
theorem canonicalLossCovariance_quadratic (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (x : Physical t) :
    RCLike.re ⟪canonicalLossCovariance t ht S x, x⟫_ℂ =
      ‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 -
        ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 := by
  have hn := (canonicalSelectedSynthesis t ht S).adjoint.apply_norm_sq_eq_inner_adjoint_left x
  have hp := (canonicalPositiveSynthesis t ht).adjoint.apply_norm_sq_eq_inner_adjoint_left x
  simp only [ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_apply] at hn hp
  simp only [canonicalLossCovariance, canonicalPositiveCovariance,
    ContinuousLinearMap.sub_apply, inner_sub_left, map_sub, ContinuousLinearMap.comp_apply]
  rw [← hn, ← hp]
private theorem finite_coefficients (F : Finset CriticalZeros) :
    FiniteDimensional ℂ (ℓ²({ρ : CriticalZeros // ρ ∈ F}, ℂ)) := by
  let L : ℓ²({ρ : CriticalZeros // ρ ∈ F}, ℂ) →ₗ[ℂ]
      ({ρ : CriticalZeros // ρ ∈ F} → ℂ) :=
    { toFun := fun f ρ => f ρ
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  apply FiniteDimensional.of_injective L
  intro f g h
  apply lp.ext
  exact h
theorem canonicalLossCovariance_compact (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) : IsCompactOperator (canonicalLossCovariance t ht S) := by
  letI : FiniteDimensional ℂ (ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) := finite_coefficients S
  exact ((isCompactOperator_of_locallyCompactSpace_rng
    (canonicalSelectedSynthesis t ht S)).comp_clm
      (canonicalSelectedSynthesis t ht S).adjoint).sub
    (canonicalPositiveCovariance_compact t ht)
end ConnesGreen
theorem solution (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (hμ : 0 < canonicalCertificateThreshold t ht S) :
    ∃ x : Physical t, x ≠ 0 ∧
      canonicalLossCovariance t ht S x = (canonicalCertificateThreshold t ht S : ℂ) • x ∧
      ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 -
        ‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 +
          canonicalCertificateThreshold t ht S * ‖x‖ ^ 2 = 0 := by
  have hm := spectrum.algebraMap_mem ℂ (canonical_positive_threshold_mem_real_spectrum t ht S hμ)
  simp only [RCLike.algebraMap_eq_ofReal] at hm
  change (canonicalCertificateThreshold t ht S : ℂ) ∈ spectrum ℂ (canonicalLossCovariance t ht S) at hm
  have hnz : (canonicalCertificateThreshold t ht S : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hμ.ne'
  have hv := ((canonicalLossCovariance_compact t ht S).hasEigenvalue_iff_mem_spectrum hnz).mpr hm
  obtain ⟨x, hx, hxn⟩ := hv.exists_hasEigenvector
  have he : canonicalLossCovariance t ht S x = (canonicalCertificateThreshold t ht S : ℂ) • x := by
    exact Module.End.mem_genEigenspace_one.mp hx
  refine ⟨x, hxn, he, ?_⟩
  have hq := canonicalLossCovariance_quadratic t ht S x
  have hscalar : RCLike.re ⟪(canonicalCertificateThreshold t ht S : ℂ) • x, x⟫_ℂ =
      canonicalCertificateThreshold t ht S * ‖x‖ ^ 2 := by
    rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
    simp [Complex.star_def, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  rw [he, hscalar] at hq
  linarith
