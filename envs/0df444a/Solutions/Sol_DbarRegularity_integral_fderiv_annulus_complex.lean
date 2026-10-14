-- Prove2me | solution 1 for DbarRegularity.integral_fderiv_annulus_complex
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T20:26:52.3568+00:00
-- url     : https://prove2.me/submissions/30ea62e1-5bd5-4345-9116-8d962f3a23e1

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Complex.Basic
import Theorems.Thm_MeasureTheory_integral_directional_derivative_annulus



namespace DbarRegularity

open MeasureTheory Metric Set

/-- Boundary integration formula on a spherical annulus in a constant direction, for a
complex-valued function that is `C¹` on the closed ball punctured at its centre. -/
theorem integral_fderiv_annulus_complex {n : ℕ} (hn : 0 < n)
    {f : EuclideanSpace ℝ (Fin n) → ℂ} {x : EuclideanSpace ℝ (Fin n)} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hf : ∀ y ∈ closedBall x R, y ≠ x → ContDiffAt ℝ 1 f y)
    (v : EuclideanSpace ℝ (Fin n)) :
    (∫ y in ball x R \ closedBall x r, fderiv ℝ f y v) =
      ((R ^ (n - 1) : ℝ) : ℂ) *
          (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            f (x + R • ω.1) * ((inner ℝ v ω.1 : ℝ) : ℂ) ∂volume.toSphere)
        - ((r ^ (n - 1) : ℝ) : ℂ) *
          (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            f (x + r • ω.1) * ((inner ℝ v ω.1 : ℝ) : ℂ) ∂volume.toSphere) := by
  -- integrability of the volume term
  have hint : IntegrableOn (fun y => fderiv ℝ f y v) (ball x R \ closedBall x r) := by
    have hK : IsCompact (closedBall x R \ ball x r) :=
      (isCompact_closedBall x R).diff isOpen_ball
    have hc : ContinuousOn (fun y => fderiv ℝ f y v) (closedBall x R \ ball x r) := by
      intro y hy
      have hyx : y ≠ x := by
        rintro rfl
        exact hy.2 (mem_ball_self hr)
      have h1 := (hf y hy.1 hyx).fderiv_right (m := 0) (by norm_num)
      exact (h1.continuousAt.clm_apply continuousAt_const).continuousWithinAt
    refine (hc.integrableOn_compact hK).mono_set ?_
    intro y hy
    exact ⟨ball_subset_closedBall hy.1, fun h => hy.2 (ball_subset_closedBall h)⟩
  -- integrability of the sphere terms
  have hsph : ∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
      Integrable (fun ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        f (x + ρ • ω.1) * ((inner ℝ v ω.1 : ℝ) : ℂ)) volume.toSphere := by
    intro ρ hρ hρR
    have hc : Continuous (fun ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        f (x + ρ • ω.1) * ((inner ℝ v ω.1 : ℝ) : ℂ)) := by
      refine Continuous.mul ?_ ?_
      · refine continuous_iff_continuousAt.2 fun ω => ?_
        have hω : ‖ω.1‖ = 1 := by simpa using ω.2
        have hmem : x + ρ • ω.1 ∈ closedBall x R := by
          rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, hω,
            Real.norm_of_nonneg hρ.le]
          linarith
        have hne : x + ρ • ω.1 ≠ x := by
          intro h
          have : ρ • ω.1 = 0 := by simpa using h
          rcases smul_eq_zero.1 this with h | h
          · exact hρ.ne' h
          · rw [h, norm_zero] at hω; exact zero_ne_one hω
        have hg : Continuous (fun ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => x + ρ • ω.1) := by
          fun_prop
        exact ContinuousAt.comp (g := f) (hf _ hmem hne).continuousAt hg.continuousAt
      · exact Complex.continuous_ofReal.comp
          (continuous_const.inner continuous_subtype_val)
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- real and imaginary parts
  have hre := MeasureTheory.integral_directional_derivative_annulus hn (f := fun y => (f y).re)
    (x := x) hr hrR (fun y hy hyx => Complex.reCLM.contDiff.contDiffAt.comp y (hf y hy hyx)) v
  have him := MeasureTheory.integral_directional_derivative_annulus hn (f := fun y => (f y).im)
    (x := x) hr hrR (fun y hy hyx => Complex.imCLM.contDiff.contDiffAt.comp y (hf y hy hyx)) v
  have hdre : ∀ y ∈ ball x R \ closedBall x r,
      fderiv ℝ (fun y => (f y).re) y v = (fderiv ℝ f y v).re := by
    intro y hy
    have hyx : y ≠ x := by
      rintro rfl
      exact hy.2 (mem_closedBall_self hr.le)
    have hd := ((hf y (ball_subset_closedBall hy.1) hyx).differentiableAt (by norm_num))
    have := (Complex.reCLM.hasFDerivAt.comp y hd.hasFDerivAt).fderiv
    change fderiv ℝ (Complex.reCLM ∘ f) y v = _
    rw [this]
    rfl
  have hdim : ∀ y ∈ ball x R \ closedBall x r,
      fderiv ℝ (fun y => (f y).im) y v = (fderiv ℝ f y v).im := by
    intro y hy
    have hyx : y ≠ x := by
      rintro rfl
      exact hy.2 (mem_closedBall_self hr.le)
    have hd := ((hf y (ball_subset_closedBall hy.1) hyx).differentiableAt (by norm_num))
    have := (Complex.imCLM.hasFDerivAt.comp y hd.hasFDerivAt).fderiv
    change fderiv ℝ (Complex.imCLM ∘ f) y v = _
    rw [this]
    rfl
  have hmeas : MeasurableSet (ball x R \ closedBall x r) :=
    measurableSet_ball.diff measurableSet_closedBall
  rw [setIntegral_congr_fun hmeas hdre] at hre
  rw [setIntegral_congr_fun hmeas hdim] at him
  have rI : (∫ y in ball x R \ closedBall x r, fderiv ℝ f y v).re =
      ∫ y in ball x R \ closedBall x r, (fderiv ℝ f y v).re := (integral_re hint).symm
  have iI : (∫ y in ball x R \ closedBall x r, fderiv ℝ f y v).im =
      ∫ y in ball x R \ closedBall x r, (fderiv ℝ f y v).im := (integral_im hint).symm
  have rS : ∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
      (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        f (x + ρ • ω.1) * ((inner ℝ v ω.1 : ℝ) : ℂ) ∂volume.toSphere).re =
      ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        (f (x + ρ • ω.1)).re * inner ℝ v ω.1 ∂volume.toSphere := by
    intro ρ hρ hρR
    have h := integral_re (hsph ρ hρ hρR)
    simp only [RCLike.re_to_complex, Complex.re_mul_ofReal] at h
    exact h.symm
  have iS : ∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
      (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        f (x + ρ • ω.1) * ((inner ℝ v ω.1 : ℝ) : ℂ) ∂volume.toSphere).im =
      ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        (f (x + ρ • ω.1)).im * inner ℝ v ω.1 ∂volume.toSphere := by
    intro ρ hρ hρR
    have h := integral_im (hsph ρ hρ hρR)
    simp only [RCLike.im_to_complex, Complex.im_mul_ofReal] at h
    exact h.symm
  apply Complex.ext
  · rw [rI, hre, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
      rS R (hr.trans hrR) le_rfl, rS r hr hrR.le]
  · rw [iI, him, Complex.sub_im, Complex.im_ofReal_mul, Complex.im_ofReal_mul,
      iS R (hr.trans hrR) le_rfl, iS r hr hrR.le]

end DbarRegularity

open DbarRegularity

open MeasureTheory Metric Set

theorem solution {n : ℕ} (hn : 0 < n)
    {f : EuclideanSpace ℝ (Fin n) → ℂ} {x : EuclideanSpace ℝ (Fin n)} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hf : ∀ y ∈ closedBall x R, y ≠ x → ContDiffAt ℝ 1 f y)
    (v : EuclideanSpace ℝ (Fin n)) :
    (∫ y in ball x R \ closedBall x r, fderiv ℝ f y v) =
      ((R ^ (n - 1) : ℝ) : ℂ) *
          (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            f (x + R • ω.1) * ((inner ℝ v ω.1 : ℝ) : ℂ) ∂volume.toSphere)
        - ((r ^ (n - 1) : ℝ) : ℂ) *
          (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            f (x + r • ω.1) * ((inner ℝ v ω.1 : ℝ) : ℂ) ∂volume.toSphere) :=
  integral_fderiv_annulus_complex hn hr hrR hf v
