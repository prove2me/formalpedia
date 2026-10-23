-- Prove2me | solution 1 for AvramDividend.Classical.positive_truncated_weighted_abs_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T21:31:05.345293+00:00
-- url     : https://prove2.me/submissions/ff97ef16-eeb0-4b77-9026-10fe706e60d4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

theorem solution
    (h : ℝ → ℝ) (w R C : ℝ)
    (hw : 0 < w) (hR : 0 < R)
    (hc : ContinuousOn h (Ioi (0 : ℝ)))
    (hb : ∀ x ∈ Ioc (0 : ℝ) R, |h x| ≤ C) :
    IntegrableOn (fun t : ℝ =>
      if t ∈ Ioc (0 : ℝ) R then
        Real.exp (-w * t) * |h t| else 0)
      (Ioi (0 : ℝ)) volume := by
  let J : Set ℝ := Ioc (0 : ℝ) R
  let F : ℝ → ℝ := fun t => Real.exp (-w * t) * |h t|
  have hcJ : ContinuousOn h J :=
    hc.mono (by intro t ht; exact ht.1)
  have hexpc : Continuous (fun t : ℝ => Real.exp (-w * t)) := by
    fun_prop
  have hFc : ContinuousOn F J := by
    change ContinuousOn (fun t : ℝ => Real.exp (-w * t) * |h t|) J
    exact hexpc.continuousOn.mul hcJ.abs
  have hFmeas : AEStronglyMeasurable F (volume.restrict J) :=
    hFc.aestronglyMeasurable measurableSet_Ioc
  have hFbound : ∀ᵐ t ∂volume.restrict J, ‖F t‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 ≤ t := le_of_lt ht.1
    have hwtx : 0 ≤ w * t := mul_nonneg hw.le ht0
    have he : Real.exp (-w * t) ≤ 1 := by
      have hu : -w * t ≤ (0 : ℝ) := by nlinarith
      simpa using (Real.exp_le_exp.mpr hu)
    have hnonneg : 0 ≤ F t :=
      mul_nonneg (le_of_lt (Real.exp_pos _)) (abs_nonneg _)
    calc
      ‖F t‖ = F t := by rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      _ ≤ |h t| := by
        dsimp [F]
        have hk := mul_le_mul_of_nonneg_right he (abs_nonneg (h t))
        simpa using hk
      _ ≤ C := hb t ht
  have hJfinite : volume J < ⊤ := by
    change volume (Ioc (0 : ℝ) R) < ⊤
    simp [Real.volume_Ioc]
  have hFi : IntegrableOn F J volume :=
    IntegrableOn.of_bound hJfinite hFmeas C hFbound
  have hFg : Integrable (J.indicator F) volume :=
    hFi.integrable_indicator measurableSet_Ioc
  have hFpos : IntegrableOn (J.indicator F) (Ioi (0 : ℝ)) volume :=
    hFg.integrableOn
  have heq :
      (fun t : ℝ => if t ∈ J then F t else 0) = J.indicator F := by
    funext t
    by_cases ht : t ∈ J
    · simp [ht, Set.indicator_of_mem]
    · simp [ht, Set.indicator_of_notMem]
  change IntegrableOn (fun t : ℝ => if t ∈ J then F t else 0)
      (Ioi (0 : ℝ)) volume
  rw [heq]
  exact hFpos
