-- Prove2me | solution 1 for FiniteEnergyPlane.setIntegral_annulus_eq_integral_circleMap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T23:06:46.125984+00:00
-- url     : https://prove2.me/submissions/79232557-240e-4932-99a0-f044bc2d18ed

import Mathlib
open MeasureTheory Metric Filter Topology Set
open scoped Real

theorem solution {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {f : ℂ → F} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hf : ContinuousOn f (closedBall 0 b \ ball 0 a)) :
    ∫ z in ball 0 b \ ball 0 a, f z = ∫ r in a..b, r • ∫ θ in 0..2 * π, f (circleMap 0 r θ) := by
  have hsymm : ∀ p : ℝ × ℝ, Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
    intro p
    rw [Complex.polarCoord_symm_apply, circleMap_zero, Complex.exp_mul_I]
    push_cast; ring
  have hnorm : ∀ r θ : ℝ, ‖circleMap 0 r θ‖ = |r| := by intro r θ; simp
  set A := ball (0 : ℂ) b \ ball 0 a
  have hA : MeasurableSet A := measurableSet_ball.diff measurableSet_ball
  set G : ℝ × ℝ → F := fun p => p.1 • f (circleMap 0 p.1 p.2)
  have step1 : ∫ z in A, f z = ∫ p in Ico a b ×ˢ Ioo (-π) π, G p := by
    rw [← integral_indicator hA, ← Complex.integral_comp_polarCoord_symm, polarCoord_target]
    have hS : Ico a b ×ˢ Ioo (-π) π = (Ioi 0 ×ˢ Ioo (-π) π) ∩ (Ico a b ×ˢ univ) := by
      ext ⟨r, θ⟩; simp only [mem_prod, mem_Ico, mem_Ioi, mem_Ioo, mem_inter_iff, mem_univ, and_true]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by linarith, h3⟩, h1, h2⟩
      · rintro ⟨⟨_, h3⟩, h1, h2⟩; exact ⟨⟨h1, h2⟩, h3⟩
    rw [hS, ← setIntegral_indicator ((measurableSet_Ico).prod MeasurableSet.univ)]
    refine setIntegral_congr_fun ((measurableSet_Ioi).prod measurableSet_Ioo) fun p hp => ?_
    have hp0 : 0 < p.1 := hp.1
    simp only [indicator, hsymm, G, mem_prod, mem_Ico, mem_univ, and_true, A, mem_diff, mem_ball,
      dist_zero_right, hnorm, abs_of_pos hp0, not_lt]
    split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; tauto) | simp
  have hcont : ContinuousOn G (Icc a b ×ˢ Icc (-π) π) := by
    apply continuousOn_fst.smul
    refine hf.comp (Continuous.continuousOn (by fun_prop)) ?_
    intro p hp
    simp only [mem_prod, mem_Icc] at hp
    simp only [mem_diff, mem_closedBall, mem_ball, dist_zero_right, hnorm, not_lt,
      abs_of_pos (lt_of_lt_of_le ha hp.1.1)]
    exact ⟨hp.1.2, hp.1.1⟩
  have hint : IntegrableOn G (Ico a b ×ˢ Ioo (-π) π) :=
    (hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ico_subset_Icc_self Ioo_subset_Icc_self)
  rw [step1, Measure.volume_eq_prod, setIntegral_prod _ hint, intervalIntegral.integral_of_le hab,
    ← integral_Ico_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Ico fun r _ => ?_
  simp only [G]
  rw [integral_smul, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  congr 1
  have := (periodic_circleMap (0 : ℂ) r).comp f
  have h2 := this.intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, zero_add] at h2
  exact h2
