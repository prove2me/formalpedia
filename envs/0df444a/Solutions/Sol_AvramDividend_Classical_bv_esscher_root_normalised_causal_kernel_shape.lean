-- Prove2me | solution 1 for AvramDividend.Classical.bv_esscher_root_normalised_causal_kernel_shape
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:23:03.034088+00:00
-- url     : https://prove2.me/submissions/aa295f9e-b42b-4f9f-a4fa-5dc47136f29c

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_subcritical_kernel_mass
import Theorems.Thm_AvramDividend_Classical_bv_esscher_positive_tail_kernel_shape_of_root
import Theorems.Thm_AvramDividend_Classical_bv_esscher_positive_tail_real_total_mass_of_root
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ κ : ℝ → ℝ,
      (∀ t : ℝ, κ t =
        if 0 < t then
          ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
            (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
            {z : ℝ≥0 | t < (z : ℝ)}) / X.drift else 0) ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      AntitoneOn κ (Ioi (0 : ℝ)) ∧
      (∀ t : ℝ, t ≤ 0 → κ t = 0) ∧
      (∀ t : ℝ, 0 ≤ κ t) ∧
      IntegrableOn κ (Ioi (0 : ℝ)) volume ∧
      (∫ t in Ioi (0 : ℝ), κ t ∂volume) < 1 := by
  obtain ⟨κ0, hκ0, hcont, hanti, hzero, hnn, hint⟩ :=
    AvramDividend.Classical.bv_esscher_positive_tail_kernel_shape_of_root X hX hbv q hq φ hφ hroot
  have hd := (AvramDividend.Classical.bv_standing_drift_pos X hX hbv).1
  have hlt := (AvramDividend.Classical.bv_esscher_root_subcritical_kernel_mass X hbv q hq φ hφ
    hroot).2
  have htot := AvramDividend.Classical.bv_esscher_positive_tail_real_total_mass_of_root X hbv q
    hq φ hφ hroot
  refine ⟨fun t => κ0 t / X.drift, fun t => ?_, hcont.div_const _, ?_, fun t ht => ?_,
    fun t => div_nonneg (hnn t) hd.le, hint.div_const _, ?_⟩
  · simp only [hκ0 t]; split_ifs <;> simp
  · intro a ha b hb hab
    exact div_le_div_of_nonneg_right (hanti ha hb hab) hd.le
  · simp [hzero t ht]
  · have hcongr : (∫ t in Ioi (0 : ℝ), κ0 t ∂volume) =
        ∫ t in Ioi (0 : ℝ), ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
          (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
          {z : ℝ≥0 | t < (z : ℝ)}) ∂volume :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht => by rw [hκ0 t, if_pos (mem_Ioi.mp ht)]
    rw [integral_div, hcongr, htot, div_lt_one hd]
    exact hlt
