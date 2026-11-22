-- Prove2me | solution 1 for AvramDividend.Classical.avram_original_strict_preruin_physical_negative_jump_discounted_value_sum_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T13:41:15.342795+00:00
-- url     : https://prove2.me/submissions/90cde8c9-dc2e-4063-8b14-71a90c0e2e65

/-
  The true finite selected pre-ruin marked jump part of the stopped
  Ito-Meyer source has nonpositive discounted value increments.
-/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_original_negative_jump_strict_preruin_spatial_mask_allcap
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys88_original_closed_cap_negative_mark_value_increment_nonpos
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (S : Finset ℝ≥0)
    (hS : ∀ t ∈ S,
      0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
      X.X t ω - Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t < 0) :
    let Y : ℝ≥0 → ℝ := fun t =>
      Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t
    (∑ t ∈ S, Real.exp (-(q * (t : ℝ))) *
      (w (Y t + (X.X t ω - Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t)) - w (Y t))) ≤ 0
:= by
  dsimp only
  refine Finset.sum_nonpos ?_
  intro t ht
  obtain ⟨htpos, htpre, hz⟩ := hS t ht
  have hMask :=
    avram_original_negative_jump_strict_preruin_spatial_mask_allcap
      X x D C hxc hD ω t htpos htpre hz
  have hChange :=
    avram_bvb_phys88_original_closed_cap_negative_mark_value_increment_nonpos
      C hC w hw_cont hw0 hw_neg hw_smooth hw_grad
      _ _ (le_of_lt hMask.1) hMask.2 hz
  exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _)) hChange
