-- Prove2me | solution 1 for AvramDividend.Classical.causal_l1_truncated_convolution_fubini_swap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T21:13:39.513511+00:00
-- url     : https://prove2.me/submissions/2e124948-c324-49fe-9a4d-813f0670535b

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AvramDividend_Classical_causal_l1_truncated_convolution_prod_integrable
import Theorems.Thm_MeasureTheory_setIntegral_integral_swap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-- Exchange the causal time integral with the lag integral on a finite horizon. -/
theorem solution
    (K g : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (x : ℝ) (hx : 0 < x) :
    (∫ t in Ioc (0 : ℝ) x,
      ∫ u : ℝ,
        ((Ioi (0 : ℝ)).indicator K) u *
        ((Ioc (0 : ℝ) x).indicator g) (t - u) ∂volume ∂volume) =
    (∫ u : ℝ,
      ∫ t in Ioc (0 : ℝ) x,
        ((Ioi (0 : ℝ)).indicator K) u *
        ((Ioc (0 : ℝ) x).indicator g) (t - u) ∂volume ∂volume) := by
  have hFull :=
    AvramDividend.Classical.causal_l1_truncated_convolution_prod_integrable K g hK hg x hx
  have hRestricted : IntegrableOn
      (fun p : ℝ × ℝ =>
        ((Ioi (0 : ℝ)).indicator K) p.2 *
        ((Ioc (0 : ℝ) x).indicator g) (p.1 - p.2))
      ((Ioc (0 : ℝ) x) ×ˢ Set.univ) (volume.prod volume) :=
    hFull.integrableOn
  have hSwap := MeasureTheory.setIntegral_integral_swap
    (fun t u : ℝ =>
      ((Ioi (0 : ℝ)).indicator K) u *
      ((Ioc (0 : ℝ) x).indicator g) (t - u))
    (s := Ioc (0 : ℝ) x) (t := Set.univ) hRestricted
  simpa using hSwap
