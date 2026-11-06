-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_BV_stopped_dominated_nonlinear_jump_source_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:36:51.231232+00:00
-- url     : https://prove2.me/submissions/956a3b18-9e79-49e1-af2d-c5b929caa844

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_absolute_raw_jump_interval_summable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (S : ℝ≥0) :
    ∀ᵐ ω ∂P,
      ∀ (w : ℝ → ℝ) (z : ℕ → ℝ≥0 → ℝ)
        (u discount : ℝ≥0 → ℝ) (L M : ℝ),
      0 ≤ L → 0 ≤ M →
      (∀ t : ℝ≥0, 0 < t ∧ t ≤ S ∧ X.X t ω - Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t ≠ 0 →
        Tendsto (fun k => z k t) atTop (nhds (u t))) →
      (∀ t : ℝ≥0, 0 < t ∧ t ≤ S ∧ X.X t ω - Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t ≠ 0 →
        ContinuousAt w (u t) ∧
        ContinuousAt w (u t + (X.X t ω - Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t))) →
      (∀ᶠ k in atTop, ∀ t : ℝ≥0, 0 < t ∧ t ≤ S ∧ X.X t ω - Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t ≠ 0 →
        |w (z k t + (X.X t ω - Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t)) - w (z k t)| ≤
          L * |X.X t ω - Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t|) →
      (∀ t : ℝ≥0, |discount t| ≤ M) →
      Tendsto
        (fun k => ∑' t : ℝ≥0,
          if 0 < t ∧ t ≤ S ∧ X.X t ω - Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t ≠ 0 then
          discount t *
            (w ((z k) t + (X.X t ω - Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t)) - w ((z k) t))
        else 0) atTop
        (nhds (∑' t : ℝ≥0,
          if 0 < t ∧ t ≤ S ∧ X.X t ω - Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t ≠ 0 then
          discount t *
            (w (u t + (X.X t ω - Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t)) - w (u t))
        else 0)) := by
  classical
  filter_upwards [avram_p3_a_bvdrift_original_absolute_raw_jump_interval_summable X hBV]
    with ω hω
  intro w z u discount L M hL hM hz hw hLip hDisc
  let d : ℝ≥0 → ℝ := fun t =>
    X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t
  have hsum : Summable (fun t : ℝ≥0 =>
      |if 0 < t ∧ t ≤ S then -d t else 0|) := by
    convert (hω 0 S (show (0 : ℝ≥0) ≤ S from zero_le)) using 1
    funext t
    by_cases ht : 0 < t ∧ t ≤ S
    · simp [ht, d, abs_sub_comm]
    · simp [ht]
  have hbound : Summable (fun t : ℝ≥0 =>
      (M * L) * |if 0 < t ∧ t ≤ S then -d t else 0|) :=
    hsum.mul_left (M * L)
  apply tendsto_tsum_of_dominated_convergence hbound
  · intro t
    by_cases ht : 0 < t ∧ t ≤ S ∧ d t ≠ 0
    · have horig : 0 < t ∧ t ≤ S ∧
        X.X t ω - Function.leftLim
          (fun r : ℝ≥0 => X.X r ω) t ≠ 0 := ht
      simp only [if_pos horig]
      have hz' := hz t horig
      have hw' := hw t horig
      have hplus : Tendsto (fun k => z k t + d t) atTop
          (nhds (u t + d t)) := hz'.add tendsto_const_nhds
      have hwa : Tendsto (fun k => w (z k t + d t)) atTop
          (nhds (w (u t + d t))) := hw'.2.tendsto.comp hplus
      have hwb : Tendsto (fun k => w (z k t)) atTop
          (nhds (w (u t))) := hw'.1.tendsto.comp hz'
      exact tendsto_const_nhds.mul (hwa.sub hwb)
    · have hneg : ¬(0 < t ∧ t ≤ S ∧
        X.X t ω - Function.leftLim
          (fun r : ℝ≥0 => X.X r ω) t ≠ 0) := ht
      simp only [if_neg hneg]
      exact tendsto_const_nhds
  · filter_upwards [hLip] with k hk
    intro t
    change ‖(if 0 < t ∧ t ≤ S ∧ d t ≠ 0 then
        discount t * (w (z k t + d t) - w (z k t))
      else 0)‖ ≤
      (M * L) * |if 0 < t ∧ t ≤ S then -d t else 0|
    by_cases ht : 0 < t ∧ t ≤ S
    · by_cases hj : d t ≠ 0
      · have hfull : 0 < t ∧ t ≤ S ∧ d t ≠ 0 :=
          ⟨ht.1, ht.2, hj⟩
        have hinc := hk t hfull
        have hmul :
            |discount t| *
                |w (z k t + d t) - w (z k t)| ≤
              (M * L) * |d t| := by
          calc
            _ ≤ M * |w (z k t + d t) - w (z k t)| :=
              mul_le_mul_of_nonneg_right (hDisc t) (abs_nonneg _)
            _ ≤ M * (L * |d t|) :=
              mul_le_mul_of_nonneg_left hinc hM
            _ = (M * L) * |d t| := by ring
        simpa only [if_pos hfull, if_pos ht, norm_mul,
          Real.norm_eq_abs, abs_neg] using hmul
      · have hd0 : d t = 0 := not_ne_iff.mp hj
        simp [hd0]
    · have hfullneg : ¬(0 < t ∧ t ≤ S ∧ d t ≠ 0) := by
        intro h
        exact ht ⟨h.1, h.2.1⟩
      simp [ht, hfullneg]
