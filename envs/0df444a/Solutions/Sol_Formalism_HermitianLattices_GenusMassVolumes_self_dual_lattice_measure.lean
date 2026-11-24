-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.self_dual_lattice_measure
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:44.176115+00:00
-- url     : https://prove2.me/submissions/b79b570d-4619-481a-8d2c-b4a55560fd0d

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourierTransformScaledInner
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.GenusMassVolumes
open MeasureTheory Module
open scoped FourierTransform
private lemma fourier_transform_scaled_inner {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] (g : V → ℂ) (ξ : V) :
    (∫ x, Complex.exp (-(2 * Real.pi * Complex.I * ((2 * inner ℝ x ξ : ℝ) : ℂ))) * g x) =
      𝓕 g ((2 : ℝ) • ξ) := by
  rw [Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, inner_smul_right]
  congr 2
  push_cast
  ring
end Formalism.HermitianLattices.GenusMassVolumes
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open MeasureTheory Module
open scoped FourierTransform
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : SelfDualMeasure := by
  intro M φ FT x
  have hFT : ∀ g ξ, FT g ξ = (2 : ℂ) ^ M * 𝓕 g ((2 : ℝ) • ξ) := by
    intro g ξ
    simp only [FT]
    rw [fourier_transform_scaled_inner]
  rw [hFT]
  have h1 : FT (φ : EuclideanSpace ℝ (Fin (2 * M)) → ℂ) =
      fun ξ => (2 : ℂ) ^ M * 𝓕 (φ : EuclideanSpace ℝ (Fin (2 * M)) → ℂ) ((2 : ℝ) • ξ) :=
    funext (hFT _)
  rw [h1, Real.fourier_eq]
  have h2 : (∫ v : EuclideanSpace ℝ (Fin (2 * M)), Real.fourierChar (-inner ℝ v ((2 : ℝ) • x)) •
        ((2 : ℂ) ^ M * 𝓕 (φ : EuclideanSpace ℝ (Fin (2 * M)) → ℂ) ((2 : ℝ) • v))) =
      ∫ v : EuclideanSpace ℝ (Fin (2 * M)),
        (fun w => Real.fourierChar (-inner ℝ w x) •
          ((2 : ℂ) ^ M * 𝓕 (φ : EuclideanSpace ℝ (Fin (2 * M)) → ℂ) w)) ((2 : ℝ) • v) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [inner_smul_left, inner_smul_right]
    simp
  rw [h2, Measure.integral_comp_smul volume (fun w => Real.fourierChar (-inner ℝ w x) •
          ((2 : ℂ) ^ M * 𝓕 (φ : EuclideanSpace ℝ (Fin (2 * M)) → ℂ) w)) (2 : ℝ)]
  have h3 : (∫ w : EuclideanSpace ℝ (Fin (2 * M)), Real.fourierChar (-inner ℝ w x) •
        ((2 : ℂ) ^ M * 𝓕 (φ : EuclideanSpace ℝ (Fin (2 * M)) → ℂ) w)) =
      (2 : ℂ) ^ M * 𝓕 (𝓕 (φ : EuclideanSpace ℝ (Fin (2 * M)) → ℂ)) x := by
    rw [Real.fourier_eq, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [Circle.smul_def, smul_eq_mul]
    ring
  rw [h3]
  have h4 : 𝓕 (𝓕 (φ : EuclideanSpace ℝ (Fin (2 * M)) → ℂ)) x = φ (-x) := by
    have := φ.continuous.fourierInv_fourier_eq φ.integrable (𝓕 φ).integrable
    have h5 := congrFun this (-x)
    rw [Real.fourierInv_eq_fourier_neg, neg_neg] at h5
    exact h5
  rw [h4]
  have hfr : finrank ℝ (EuclideanSpace ℝ (Fin (2 * M))) = 2 * M := by simp
  rw [hfr, abs_of_pos (by positivity), Complex.real_smul]
  push_cast
  have h2M : ((2 : ℂ) ^ M) ≠ 0 := pow_ne_zero _ two_ne_zero
  have h22 : ((2 : ℂ) ^ (2 * M)) = 2 ^ M * 2 ^ M := by rw [two_mul, pow_add]
  generalize φ (-x) = c
  rw [h22]
  field_simp
end Formalism.HermitianLattices.GenusMassVolumes
