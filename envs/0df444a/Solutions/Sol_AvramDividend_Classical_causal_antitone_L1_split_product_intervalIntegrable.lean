-- Prove2me | solution 1 for AvramDividend.Classical.causal_antitone_L1_split_product_intervalIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T16:05:56.615374+00:00
-- url     : https://prove2.me/submissions/78bfdbd0-05f0-48f9-8116-9f9465f9a13a

import Mathlib.Analysis.Convolution
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_causal_positive_L1_intervalIntegrable
import Theorems.Thm_AvramDividend_Classical_causal_reflected_kernel_right_interval_integrable
import Theorems.Thm_AvramDividend_Classical_causal_antitone_split_product_integrable_of_pointwise_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Positive convolution products are integrable after a midpoint split. -/
theorem solution
    (κ F : ℝ → ℝ) (x A : ℝ) (hx : 0 < x) (hA : 0 ≤ A)
    (hκanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hκcont : ContinuousOn κ (Ioi (0 : ℝ)))
    (hκnonneg : ∀ t : ℝ, 0 < t → 0 ≤ κ t)
    (hκL1 : IntegrableOn κ (Ioi (0 : ℝ)) volume)
    (hFnonneg : ∀ s : ℝ, 0 < s → 0 ≤ F s)
    (hFpoint : ∀ s : ℝ, 0 < s → F s ≤ A / s)
    (hFL1 : IntegrableOn F (Ioi (0 : ℝ)) volume) :
    IntervalIntegrable (fun s : ℝ => κ (x - s) * F s) volume 0 x := by
  let u : ℝ := x / 2
  have hu : 0 < u := by dsimp [u]; linarith
  have hux : u < x := by dsimp [u]; linarith
  have hFleft : IntegrableOn F (Ioc (0 : ℝ) u) volume :=
    hFL1.mono_set (by
      intro s hs
      exact hs.1)
  have hKleftMeas : AEStronglyMeasurable
      (fun s : ℝ => κ (x - s))
      (volume.restrict (Ioc (0 : ℝ) u)) := by
    have hm : MapsTo (fun s : ℝ => x - s)
        (Ioc (0 : ℝ) u) (Ioi (0 : ℝ)) := by
      intro s hs
      exact sub_pos.mpr (lt_of_le_of_lt hs.2 hux)
    have hsub : ContinuousOn (fun s : ℝ => x - s)
        (Ioc (0 : ℝ) u) :=
      (continuous_const.sub continuous_id).continuousOn
    have hc : ContinuousOn (fun s : ℝ => κ (x - s))
        (Ioc (0 : ℝ) u) := hκcont.comp hsub hm
    exact hc.aestronglyMeasurable measurableSet_Ioc
  have hKright : IntegrableOn (fun s : ℝ => κ (x - s))
      (Ioc u x) volume := by
    have hxu : 0 < x - u := sub_pos.mpr hux
    have hint := causal_positive_L1_intervalIntegrable κ hκL1 (x - u) hxu
    have hr := causal_reflected_kernel_right_interval_integrable κ x u hint
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hux.le).1 hr
  have hFright : AEStronglyMeasurable F
      (volume.restrict (Ioc u x)) := by
    have hs : Ioc u x ⊆ Ioi (0 : ℝ) := by
      intro s hs
      exact lt_trans hu hs.1
    exact (hFL1.mono_set hs).aestronglyMeasurable
  have hsplit :=
    causal_antitone_split_product_integrable_of_pointwise_bound
      κ F x u A hu hux hA hκanti hκnonneg hFnonneg hFpoint
      hFleft hKleftMeas hKright hFright
  exact hsplit.1.trans hsplit.2
