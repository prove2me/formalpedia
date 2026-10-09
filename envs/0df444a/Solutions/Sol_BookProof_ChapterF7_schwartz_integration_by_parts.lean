-- Prove2me | solution 1 for BookProof.ChapterF7.schwartz_integration_by_parts
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:08:24.420924+00:00
-- url     : https://prove2.me/submissions/27a9ace9-3b47-47b4-af1c-30ad07e19a2c

-- Generated from ChapterF7.lean — solution of BookProof.ChapterF7.schwartz_integration_by_parts
import Mathlib
import Definitions.Def_ChapterF7
open BookProof.ChapterF7



open SchwartzMap MeasureTheory Complex
open scoped BigOperators


noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (f g : 𝓢(ℝ, ℂ)) :
    (∫ x, (starRingEnd ℂ) (deriv (f : ℝ → ℂ) x) * g x)
      = - ∫ x, (starRingEnd ℂ) (f x) * deriv (g : ℝ → ℂ) x := by

  have hcdf : Continuous (fun x => (starRingEnd ℂ) (deriv (f : ℝ → ℂ) x)) := by
    have h : (fun x => (starRingEnd ℂ) (deriv (f : ℝ → ℂ) x))
        = fun x => (starRingEnd ℂ) ((SchwartzMap.derivCLM ℝ ℂ f) x) := by
      funext x; rw [SchwartzMap.derivCLM_apply]
    rw [h]; exact Complex.continuous_conj.comp (SchwartzMap.derivCLM ℝ ℂ f).continuous
  have hdu : ∀ x, HasDerivAt (fun t => (starRingEnd ℂ) (f t))
      ((starRingEnd ℂ) (deriv (f : ℝ → ℂ) x)) x := by
    intro x
    simpa using (f.differentiableAt.hasDerivAt (x := x)).star
  have hdv : ∀ x, HasDerivAt (g : ℝ → ℂ) (deriv (g : ℝ → ℂ) x) x :=
    fun x => g.differentiableAt.hasDerivAt
  have h1 : Integrable (fun x => (starRingEnd ℂ) (deriv (f : ℝ → ℂ) x) * g x) volume := by
    obtain ⟨C, _, hC⟩ := (SchwartzMap.derivCLM ℝ ℂ f).decay 0 0
    refine (g.integrable (μ := volume)).bdd_mul (c := C) hcdf.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    have hh : ‖(starRingEnd ℂ) (deriv (f : ℝ → ℂ) x)‖ = ‖(SchwartzMap.derivCLM ℝ ℂ f) x‖ := by
      rw [SchwartzMap.derivCLM_apply]; simp
    rw [hh]; simpa using hC x
  have h2 : Integrable (fun x => (starRingEnd ℂ) (f x) * deriv (g : ℝ → ℂ) x) volume := by
    obtain ⟨C, _, hC⟩ := f.decay 0 0
    have hig : Integrable (fun x => deriv (g : ℝ → ℂ) x) volume := by
      refine (SchwartzMap.derivCLM ℝ ℂ g).integrable.congr
        (Filter.Eventually.of_forall fun x => ?_)
      rw [SchwartzMap.derivCLM_apply]
    refine hig.bdd_mul (c := C)
      (Complex.continuous_conj.comp f.continuous).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun x => by simpa using hC x)
  have hbot : Filter.Tendsto ((fun t => (starRingEnd ℂ) (f t)) * (g : ℝ → ℂ))
      Filter.atBot (nhds 0) := by
    have huc : Filter.Tendsto (fun t => (starRingEnd ℂ) (f t)) Filter.atBot (nhds 0) := by
      have h := (Complex.continuous_conj.tendsto (0 : ℂ)).comp
        (f.tendsto_cocompact.mono_left atBot_le_cocompact)
      rw [map_zero] at h
      exact h
    have hvc : Filter.Tendsto (g : ℝ → ℂ) Filter.atBot (nhds 0) :=
      g.tendsto_cocompact.mono_left atBot_le_cocompact
    have hm := huc.mul hvc
    rw [show (0 : ℂ) * 0 = 0 by ring] at hm
    convert hm using 1
    funext t
    rfl
  have htop : Filter.Tendsto ((fun t => (starRingEnd ℂ) (f t)) * (g : ℝ → ℂ))
      Filter.atTop (nhds 0) := by
    have huc : Filter.Tendsto (fun t => (starRingEnd ℂ) (f t)) Filter.atTop (nhds 0) := by
      have h := (Complex.continuous_conj.tendsto (0 : ℂ)).comp
        (f.tendsto_cocompact.mono_left atTop_le_cocompact)
      rw [map_zero] at h
      exact h
    have hvc : Filter.Tendsto (g : ℝ → ℂ) Filter.atTop (nhds 0) :=
      g.tendsto_cocompact.mono_left atTop_le_cocompact
    have hm := huc.mul hvc
    rw [show (0 : ℂ) * 0 = 0 by ring] at hm
    convert hm using 1
    funext t
    rfl
  have key := integral_deriv_mul_eq_sub (fun x _ => hdu x) (fun x _ => hdv x)
    (h1.add h2) hbot htop
  simp only [sub_self] at key
  rw [integral_add h1 h2] at key
  exact eq_neg_of_add_eq_zero_left key
