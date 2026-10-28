-- Prove2me | solution 1 for FiniteEnergyPlane.contDiffOn_isJHolomorphicOn_comp_mul
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-24T21:23:27.172737+00:00
-- url     : https://prove2.me/submissions/d6f54dc1-5d9e-4b4a-ae88-e0614c1d93a1

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem contDiffOn_isJHolomorphicOn_comp_mul_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (J : E → E →L[ℝ] E) (ρ : ℝ) (hρ : 0 < ρ) (v : ℂ → E)
    (hv : ContDiffOn ℝ ∞ v (ball 0 ρ \ {0}))
    (hhol : JHolomorphic.IsJHolomorphicOn J (ball 0 ρ \ {0}) v) :
    ContDiffOn ℝ ∞ (fun z => v ((ρ : ℂ) * z)) (ball 0 1 \ {0}) ∧
      JHolomorphic.IsJHolomorphicOn J (ball 0 1 \ {0}) (fun z => v ((ρ : ℂ) * z)) ∧
      (∀ z, fderiv ℝ (fun z => v ((ρ : ℂ) * z)) z = ρ • fderiv ℝ v ((ρ : ℂ) * z)) ∧
      ∫⁻ z in ball 0 1 \ {0}, ENNReal.ofReal (‖fderiv ℝ (fun z => v ((ρ : ℂ) * z)) z‖ ^ 2) =
        ∫⁻ z in ball 0 ρ \ {0}, ENNReal.ofReal (‖fderiv ℝ v z‖ ^ 2) := by
  set e : ℂ ≃L[ℝ] ℂ := (LinearEquiv.smulOfNeZero ℝ ℂ ρ hρ.ne').toContinuousLinearEquiv with he
  have heap : ∀ z, e z = (ρ : ℂ) * z := fun z => by
    simp [he, Complex.real_smul]
  have hw : (fun z => v ((ρ : ℂ) * z)) = v ∘ e := by
    funext z; simp [heap]
  have hpre : e ⁻¹' (ball (0 : ℂ) ρ \ {0}) = ball 0 1 \ {0} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_diff, mem_ball, dist_zero_right, Set.mem_singleton_iff,
      heap, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ.le, mul_eq_zero,
      Complex.ofReal_eq_zero, hρ.ne', false_or]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by nlinarith [norm_nonneg z], h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by nlinarith [norm_nonneg z], h2⟩
  have hmaps : Set.MapsTo e (ball 0 1 \ {0}) (ball 0 ρ \ {0}) := by
    intro z hz; rw [← hpre] at hz; exact hz
  have hD : ∀ z, fderiv ℝ (fun z => v ((ρ : ℂ) * z)) z = ρ • fderiv ℝ v ((ρ : ℂ) * z) := by
    intro z
    rw [hw, e.comp_right_fderiv, heap]
    ext h
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearEquiv.coe_coe, heap]
    rw [show (ρ : ℂ) * h = ρ • h from Complex.real_smul.symm, map_smul]
  refine ⟨?_, ?_, hD, ?_⟩
  · rw [hw]; exact hv.comp e.contDiff.contDiffOn hmaps
  · intro z hz
    have hz' := hmaps hz
    obtain ⟨hd, hdb⟩ := hhol (e z) hz'
    refine ⟨?_, ?_⟩
    · rw [hw]; exact hd.comp z e.differentiableAt
    · unfold JHolomorphic.dbarJ at hdb ⊢
      rw [hD z]
      rw [heap] at hdb
      simp only [ContinuousLinearMap.smul_apply, map_smul]
      rw [← smul_add, hdb, smul_zero]
  · simp_rw [hD, norm_smul, Real.norm_of_nonneg hρ.le, mul_pow]
    have hme : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
    have hmap : Measure.map e volume = ENNReal.ofReal (|ρ ^ 2|⁻¹) • (volume : Measure ℂ) := by
      have := Measure.map_addHaar_smul (volume : Measure ℂ) hρ.ne'
      rw [Complex.finrank_real_complex] at this
      convert this using 2
      · rfl
      · funext x; rw [heap, Complex.real_smul]
      · rw [abs_inv]
    have key : ∫⁻ y in ball 0 ρ \ {0}, ENNReal.ofReal (ρ ^ 2 * ‖fderiv ℝ v y‖ ^ 2)
        ∂(Measure.map e volume) = ∫⁻ z in ball 0 1 \ {0},
          ENNReal.ofReal (ρ ^ 2 * ‖fderiv ℝ v ((ρ : ℂ) * z)‖ ^ 2) := by
      rw [hme.restrict_map, hme.lintegral_map, hpre]
      simp only [heap]
    rw [← key, hmap, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
    simp_rw [ENNReal.ofReal_mul (sq_nonneg ρ)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, ← ENNReal.ofReal_mul
      (inv_nonneg.2 (abs_nonneg _)), abs_of_nonneg (sq_nonneg ρ),
      inv_mul_cancel₀ (pow_ne_zero 2 hρ.ne'), ENNReal.ofReal_one, one_mul]

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (J : E → E →L[ℝ] E) (ρ : ℝ) (hρ : 0 < ρ) (v : ℂ → E)
    (hv : ContDiffOn ℝ ∞ v (ball 0 ρ \ {0}))
    (hhol : JHolomorphic.IsJHolomorphicOn J (ball 0 ρ \ {0}) v) :
    ContDiffOn ℝ ∞ (fun z => v ((ρ : ℂ) * z)) (ball 0 1 \ {0}) ∧
      JHolomorphic.IsJHolomorphicOn J (ball 0 1 \ {0}) (fun z => v ((ρ : ℂ) * z)) ∧
      (∀ z, fderiv ℝ (fun z => v ((ρ : ℂ) * z)) z = ρ • fderiv ℝ v ((ρ : ℂ) * z)) ∧
      ∫⁻ z in ball 0 1 \ {0}, ENNReal.ofReal (‖fderiv ℝ (fun z => v ((ρ : ℂ) * z)) z‖ ^ 2) =
        ∫⁻ z in ball 0 ρ \ {0}, ENNReal.ofReal (‖fderiv ℝ v z‖ ^ 2) :=
  contDiffOn_isJHolomorphicOn_comp_mul_aux J ρ hρ v hv hhol
