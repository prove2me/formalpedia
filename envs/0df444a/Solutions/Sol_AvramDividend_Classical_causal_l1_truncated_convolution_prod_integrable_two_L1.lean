-- Prove2me | solution 1 for AvramDividend.Classical.causal_l1_truncated_convolution_prod_integrable_two_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T20:01:27.054469+00:00
-- url     : https://prove2.me/submissions/4222faa1-4857-49b0-87c6-05343ff9b51f

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Finite-horizon causal convolution products are integrable for two L1 inputs. -/
theorem solution
    (K g : ℝ → ℝ) (x : ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : IntegrableOn g (Ioc (0 : ℝ) x) volume) :
    Integrable (fun p : ℝ × ℝ =>
      ((Ioi (0 : ℝ)).indicator K) p.2 *
      ((Ioc (0 : ℝ) x).indicator g) (p.1 - p.2))
      (volume.prod volume) := by
  have hKi : Integrable ((Ioi (0 : ℝ)).indicator K) volume :=
    (integrable_indicator_iff measurableSet_Ioi).2 hK
  have hgi : Integrable ((Ioc (0 : ℝ) x).indicator g) volume :=
    (integrable_indicator_iff measurableSet_Ioc).2 hg
  exact Integrable.convolution_integrand
    (ContinuousLinearMap.mul ℝ ℝ) hKi hgi
