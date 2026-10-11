-- Prove2me | solution 1 for BookProof.RadialMollifier.polar_radial
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:51:20.152241+00:00
-- url     : https://prove2.me/submissions/90df544d-4dd2-479a-85d9-06882af75186

-- Generated from ChapterRadialMollifier.lean — solution of BookProof.RadialMollifier.polar_radial
import Mathlib
import Definitions.Def_ChapterRadialMollifier
import Theorems.Thm_BookProof_RadialMollifier_moll_continuous
import Theorems.Thm_BookProof_RadialMollifier_moll_eq_zero_of_le
import Theorems.Thm_BookProof_RadialMollifier_continuous_polarSymm
import Theorems.Thm_BookProof_RadialMollifier_moll_polarSymm
open BookProof.RadialMollifier




open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {δ : ℝ} (hδ : 0 < δ) (G : ℂ → ℂ) (hG : Continuous G) :
    ∫ u : ℂ, (moll δ u : ℂ) * G u
      = ∫ r in Ioi (0 : ℝ), ((r * moll δ r : ℝ) : ℂ) *
          ∫ θ in (-π)..π, G (Complex.polarCoord.symm (r, θ)) := by

  classical
  set f : ℂ → ℂ := fun u => (moll δ u : ℂ) * G u with hf
  set F : ℝ × ℝ → ℂ := fun p => p.1 • f (Complex.polarCoord.symm p) with hF
  have hFcont : Continuous F := by
    refine Continuous.smul continuous_fst ?_
    exact (Continuous.mul (Complex.continuous_ofReal.comp
      ((moll_continuous δ).comp continuous_polarSymm)) (hG.comp continuous_polarSymm))
  -- the integrand vanishes unless `|p.1| < δ`
  have hvanish : ∀ p : ℝ × ℝ, δ ≤ |p.1| → F p = 0 := by
    intro p hp
    have : moll δ (Complex.polarCoord.symm p) = 0 := by
      refine moll_eq_zero_of_le hδ ?_
      rw [Complex.norm_polarCoord_symm]
      exact hp
    change p.1 • ((moll δ (Complex.polarCoord.symm p) : ℂ) * G _) = 0
    rw [this]
    simp
  -- integrability on the polar target
  have hint : IntegrableOn F (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) (volume.prod volume) := by
    have hmeas : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) :=
      measurableSet_Ioi.prod measurableSet_Ioo
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-δ, -π)) (b := (δ, π))).exists_bound_of_continuousOn
      hFcont.continuousOn
    rw [← integrable_indicator_iff hmeas]
    refine Integrable.mono' (g := (Icc (-δ, -π) (δ, π)).indicator (fun _ => max C 0)) ?_
      (hFcont.aestronglyMeasurable.indicator hmeas) ?_
    · rw [integrable_indicator_iff measurableSet_Icc]
      exact integrableOn_const (C := max C 0) (by
        refine ne_of_lt ?_
        exact (measure_Icc_lt_top (μ := (volume : Measure (ℝ × ℝ))))) |>.mono_set (le_refl _)
    · filter_upwards with p
      by_cases hp : p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-π) π
      · rw [Set.indicator_of_mem hp]
        by_cases hp1 : δ ≤ |p.1|
        · rw [hvanish p hp1]
          simpa using Set.indicator_apply_nonneg (a := p)
            (fun _ => le_max_right C 0)
        · have hmem : p ∈ Icc (-δ, -π) (δ, π) := by
            obtain ⟨hp1', hp2⟩ := hp
            simp only [mem_Icc, Prod.le_def]
            push_neg at hp1
            constructor
            · exact ⟨by cases abs_lt.1 hp1 with | intro h1 h2 => linarith,
                le_of_lt (mem_Ioo.1 hp2).1⟩
            · exact ⟨le_of_lt (abs_lt.1 hp1).2, le_of_lt (mem_Ioo.1 hp2).2⟩
          rw [Set.indicator_of_mem hmem]
          exact le_trans (hC p hmem) (le_max_left _ _)
      · rw [Set.indicator_of_notMem hp]
        simp only [norm_zero]
        exact Set.indicator_apply_nonneg fun _ => le_max_right _ _
  have key : (∫ p in Complex.polarCoord.target, F p) = ∫ u : ℂ, f u :=
    Complex.integral_comp_polarCoord_symm f
  rw [← key, Complex.polarCoord_target, Measure.volume_eq_prod, setIntegral_prod F hint]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro r hr
  have hr0 : 0 < r := hr
  have hinner : ∀ θ : ℝ,
      F (r, θ) = ((r * moll δ r : ℝ) : ℂ) * G (Complex.polarCoord.symm (r, θ)) := by
    intro θ
    simp only [hF, hf, moll_polarSymm hr0, Complex.real_smul, Complex.ofReal_mul]
    ring
  simp only [hinner]
  rw [MeasureTheory.integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (-π : ℝ) ≤ π)]
