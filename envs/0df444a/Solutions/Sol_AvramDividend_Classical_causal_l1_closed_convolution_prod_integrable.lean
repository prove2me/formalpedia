-- Prove2me | solution 1 for AvramDividend.Classical.causal_l1_closed_convolution_prod_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T21:49:20.788295+00:00
-- url     : https://prove2.me/submissions/8c154114-fa70-48fb-b5f2-f42fb5bb8b67

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (K g : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (x : ℝ) (hx : 0 < x) :
    Integrable (fun p : ℝ × ℝ =>
      ((Ioi (0 : ℝ)).indicator K) p.2 *
      ((Icc (0 : ℝ) x).indicator g) (p.1 - p.2))
      (volume.prod volume) := by
  have hKi : Integrable ((Ioi (0 : ℝ)).indicator K) volume :=
    (integrable_indicator_iff measurableSet_Ioi).2 hK
  have hcont : ContinuousOn g (Icc (0 : ℝ) x) :=
    hg.mono (by intro s hs; exact hs.1)
  have hgi : IntegrableOn g (Icc (0 : ℝ) x) volume :=
    hcont.integrableOn_Icc
  have hgt : Integrable ((Icc (0 : ℝ) x).indicator g) volume :=
    (integrable_indicator_iff measurableSet_Icc).2 hgi
  exact Integrable.convolution_integrand
    (ContinuousLinearMap.mul ℝ ℝ) hKi hgt
