-- Prove2me | solution 1 for BookProof.ChapterF7.momentum_l2Symmetric
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:07:11.60397+00:00
-- url     : https://prove2.me/submissions/4597a24a-2c6a-4b53-a454-37a1b15b24d5

-- Generated from ChapterF7.lean — theorem BookProof.ChapterF7.momentum_l2Symmetric
import Mathlib
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitary
open BookProof.ChapterF7


open SchwartzMap MeasureTheory Complex
open scoped BigOperators


noncomputable section
open BookProof.ChapterF7

theorem solution: IsL2Symmetric momentum := by
  intro f g
  have hb : ∀ h : 𝓢(ℝ, ℂ), ∀ x, ‖h x‖ ≤ ‖h.toBoundedContinuousFunction‖ := fun h x => by
    simpa using h.toBoundedContinuousFunction.norm_coe_le_norm x
  have ider : ∀ h : 𝓢(ℝ, ℂ), MeasureTheory.Integrable (fun x => deriv h x) := fun h => by
    have e : (fun x => deriv h x) = ⇑(SchwartzMap.derivCLM ℂ ℂ h) := by
      funext x; simp [SchwartzMap.derivCLM_apply]
    rw [e]
    exact SchwartzMap.integrable _
  have key : ∫ x, starRingEnd ℂ (f x) * deriv g x = -∫ x, starRingEnd ℂ (deriv f x) * g x := by
    refine integral_mul_deriv_eq_deriv_mul_of_integrable
      (u := fun x => starRingEnd ℂ (f x)) (v := fun x => g x)
      (fun x _ => (f.hasDerivAt x).star) (fun x _ => g.hasDerivAt x) ?_ ?_ ?_
    · exact (ider g).bdd_mul (c := ‖f.toBoundedContinuousFunction‖)
        (f.continuous.star.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => by
          simpa using hb f x)
    · exact g.integrable.bdd_mul (c := ‖(SchwartzMap.derivCLM ℂ ℂ f).toBoundedContinuousFunction‖)
        ((SchwartzMap.derivCLM ℂ ℂ f).continuous.star.aestronglyMeasurable.congr
          (Filter.Eventually.of_forall fun x => by simp [SchwartzMap.derivCLM_apply]))
        (Filter.Eventually.of_forall fun x => by
          simpa [SchwartzMap.derivCLM_apply] using hb (SchwartzMap.derivCLM ℂ ℂ f) x)
    · exact g.integrable.bdd_mul (c := ‖f.toBoundedContinuousFunction‖)
        (f.continuous.star.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => by
          simpa using hb f x)
  unfold l2pair BookProof.ChapterF7.momentum
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, SchwartzMap.smul_apply,
    SchwartzMap.derivCLM_apply, smul_eq_mul]
  have e1 : (fun x => starRingEnd ℂ (-Complex.I * deriv f x) * g x)
      = fun x => Complex.I * (starRingEnd ℂ (deriv f x) * g x) := by
    funext x; simp [map_mul, Complex.conj_I]; ring
  have e2 : (fun x => starRingEnd ℂ (f x) * (-Complex.I * deriv g x))
      = fun x => (-Complex.I) * (starRingEnd ℂ (f x) * deriv g x) := by
    funext x; ring
  rw [e1, e2, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, key]
  ring
