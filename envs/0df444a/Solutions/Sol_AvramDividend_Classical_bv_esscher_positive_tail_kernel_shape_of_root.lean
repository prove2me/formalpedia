-- Prove2me | solution 1 for AvramDividend.Classical.bv_esscher_positive_tail_kernel_shape_of_root
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T08:52:21.704005+00:00
-- url     : https://prove2.me/submissions/232d6442-2a18-42d1-aaea-5ccfdf07239f

import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_subcritical_kernel_mass
import Theorems.Thm_AvramDividend_Classical_esscher_tail_kernel_mass_as_discounted_first_moment
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_density_total_mass
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_real_antitone_of_finite_firstMoment
import Theorems.Thm_AvramDividend_Classical_bv_esscher_positive_magnitude_tail_continuous
import Theorems.Thm_AvramDividend_Classical_bv_esscher_positive_tail_real_integrable_of_root
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ κ : ℝ → ℝ,
      (∀ t : ℝ, κ t = if 0 < t then ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
      (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
      {z : ℝ≥0 | t < (z : ℝ)}) else 0) ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      AntitoneOn κ (Ioi (0 : ℝ)) ∧
      (∀ t : ℝ, t ≤ 0 → κ t = 0) ∧
      (∀ t : ℝ, 0 ≤ κ t) ∧
      IntegrableOn κ (Ioi (0 : ℝ)) volume := by
  set μ := X.ν.map (fun y : ℝ => Real.toNNReal (-y))
  set μφ := μ.withDensity (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))))
  set T : ℝ → ℝ := fun t => (μφ {z : ℝ≥0 | t < (z : ℝ)}).toReal with hT
  have heq : EqOn (fun t : ℝ => if 0 < t then T t else 0) T (Ioi (0 : ℝ)) :=
    fun t ht => if_pos ht
  have hfirst : (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μφ) < ⊤ := by
    rw [← AvramDividend.Classical.positive_jump_tail_density_total_mass,
      AvramDividend.Classical.esscher_tail_kernel_mass_as_discounted_first_moment μ φ]
    exact (AvramDividend.Classical.bv_esscher_root_subcritical_kernel_mass X hbv q hq φ hφ
      hroot).1.lintegral_lt_top
  refine ⟨fun t => if 0 < t then T t else 0, fun t => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact (AvramDividend.Classical.bv_esscher_positive_magnitude_tail_continuous X hX hbv φ
      hφ.le).congr heq
  · intro a ha b hb hab
    rw [heq ha, heq hb]
    exact AvramDividend.Classical.positive_jump_tail_real_antitone_of_finite_firstMoment μφ
      hfirst ha hb hab
  · intro t ht
    exact if_neg (not_lt.mpr ht)
  · intro t
    dsimp only
    split_ifs
    · exact ENNReal.toReal_nonneg
    · exact le_rfl
  · exact (AvramDividend.Classical.bv_esscher_positive_tail_real_integrable_of_root X hbv q hq φ
      hφ hroot).congr_fun heq.symm measurableSet_Ioi
