-- Prove2me | solution 1 for BookProof.HalfLineLimitCircle.integral_deriv2_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:38:35.906555+00:00
-- url     : https://prove2.me/submissions/eefc9b50-c867-4ec1-b945-1c7507f5198d

-- Generated from ChapterHalfLineLimitCircle.lean — solution of BookProof.HalfLineLimitCircle.integral_deriv2_mul
import Mathlib
import Definitions.Def_ChapterHalfLineLimitCircle
import Theorems.Thm_BookProof_HalfLineLimitCircle_hasCompactSupport_conj
import Theorems.Thm_BookProof_HalfLineLimitCircle_setIntegral_eq_integral_of_testSpace
import Definitions.Def_ChapterFarisLavine
open BookProof.HalfLineLimitCircle




open MeasureTheory Set BookProof.FarisLavine

noncomputable section

local notation "smoothTop" => ((⊤ : ℕ∞) : WithTop ℕ∞)

set_option maxHeartbeats 1000000 in
theorem solution (f : ℝ → ℂ) (hf : f ∈ testSpace) (w : ℝ → ℂ)
    (hw : ContDiff ℝ smoothTop w) :
    ∫ x in Ioi (0 : ℝ), (starRingEnd ℂ) (deriv (deriv f) x) * w x
      = ∫ x in Ioi (0 : ℝ), (starRingEnd ℂ) (f x) * deriv (deriv w) x := by

  classical
  have hfc := contDiff_of_mem_testSpace hf
  have hf_prime := (contDiff_infty_iff_deriv.mp hfc).2
  have hf'' := (contDiff_infty_iff_deriv.mp hf_prime).2
  have hw' := (contDiff_infty_iff_deriv.mp hw).2
  have hw'' := (contDiff_infty_iff_deriv.mp hw').2
  -- the antiderivative of the difference
  set F : ℝ → ℂ := fun x =>
    (starRingEnd ℂ) (deriv f x) * w x - (starRingEnd ℂ) (f x) * deriv w x with hF
  set G : ℝ → ℂ := fun x =>
    (starRingEnd ℂ) (deriv (deriv f) x) * w x - (starRingEnd ℂ) (f x) * deriv (deriv w) x with hG
  have hderiv : ∀ x, HasDerivAt F (G x) x := by
    intro x
    have h1 : HasDerivAt (fun y => (starRingEnd ℂ) (deriv f y))
        ((starRingEnd ℂ) (deriv (deriv f) x)) x :=
      ((hf_prime.differentiable (by simp)).differentiableAt.hasDerivAt).star
    have h2 : HasDerivAt w (deriv w x) x :=
      (hw.differentiable (by simp)).differentiableAt.hasDerivAt
    have h3 : HasDerivAt (fun y => (starRingEnd ℂ) (f y)) ((starRingEnd ℂ) (deriv f x)) x :=
      ((hfc.differentiable (by simp)).differentiableAt.hasDerivAt).star
    have h4 : HasDerivAt (deriv w) (deriv (deriv w) x) x :=
      (hw'.differentiable (by simp)).differentiableAt.hasDerivAt
    have := (h1.mul h2).sub (h3.mul h4)
    refine this.congr_deriv ?_
    simp only [hG]
    ring
  have hFsupp : HasCompactSupport F := by
    refine HasCompactSupport.sub ?_ ?_
    · exact HasCompactSupport.mul_right
        (hasCompactSupport_conj (hasCompactSupport_of_mem_testSpace hf).deriv)
    · exact HasCompactSupport.mul_right
        (hasCompactSupport_conj (hasCompactSupport_of_mem_testSpace hf))
  have hGsupp : HasCompactSupport G := by
    refine HasCompactSupport.sub ?_ ?_
    · exact HasCompactSupport.mul_right
        (hasCompactSupport_conj (hasCompactSupport_of_mem_testSpace hf).deriv.deriv)
    · exact HasCompactSupport.mul_right
        (hasCompactSupport_conj (hasCompactSupport_of_mem_testSpace hf))
  have hFcont : Continuous F := by
    refine Continuous.sub (Continuous.mul ?_ hw.continuous) (Continuous.mul ?_ hw'.continuous)
    · exact Complex.continuous_conj.comp hf_prime.continuous
    · exact Complex.continuous_conj.comp hfc.continuous
  have hGcont : Continuous G := by
    refine Continuous.sub (Continuous.mul ?_ hw.continuous) (Continuous.mul ?_ hw''.continuous)
    · exact Complex.continuous_conj.comp hf''.continuous
    · exact Complex.continuous_conj.comp hfc.continuous
  have hzero : ∫ x, G x = 0 :=
    integral_eq_zero_of_hasDerivAt_of_integrable hderiv
      (hGcont.integrable_of_hasCompactSupport hGsupp)
      (hFcont.integrable_of_hasCompactSupport hFsupp)
  have hsplit : ∫ x, G x
      = (∫ x, (starRingEnd ℂ) (deriv (deriv f) x) * w x)
        - ∫ x, (starRingEnd ℂ) (f x) * deriv (deriv w) x := by
    refine integral_sub ?_ ?_
    · exact Continuous.integrable_of_hasCompactSupport
        (Continuous.mul (Complex.continuous_conj.comp hf''.continuous) hw.continuous)
        (HasCompactSupport.mul_right
          (hasCompactSupport_conj (hasCompactSupport_of_mem_testSpace hf).deriv.deriv))
    · exact Continuous.integrable_of_hasCompactSupport
        (Continuous.mul (Complex.continuous_conj.comp hfc.continuous) hw''.continuous)
        (HasCompactSupport.mul_right
          (hasCompactSupport_conj (hasCompactSupport_of_mem_testSpace hf)))
  rw [setIntegral_eq_integral_of_testSpace (deriv_mem_testSpace (deriv_mem_testSpace hf)) w,
    setIntegral_eq_integral_of_testSpace hf (deriv (deriv w))]
  have hAB : (∫ x, (starRingEnd ℂ) (deriv (deriv f) x) * w x)
      - ∫ x, (starRingEnd ℂ) (f x) * deriv (deriv w) x = 0 := by
    rw [← hsplit]; exact hzero
  exact sub_eq_zero.mp hAB
