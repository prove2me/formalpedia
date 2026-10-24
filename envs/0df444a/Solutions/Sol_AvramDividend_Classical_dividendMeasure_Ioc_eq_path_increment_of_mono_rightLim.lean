-- Prove2me | solution 1 for AvramDividend.Classical.dividendMeasure_Ioc_eq_path_increment_of_mono_rightLim
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T12:00:03.420994+00:00
-- url     : https://prove2.me/submissions/6b331af2-c53f-4cc6-8019-ba18a18ae4a6

import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A right-limit-fixed monotone path has its ordinary Stieltjes interval increment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (s t : ℝ)
    (hm : Monotone (fun r : ℝ => D r.toNNReal ω))
    (hr : ∀ r : ℝ,
      Function.rightLim (fun v : ℝ => D v.toNNReal ω) r = D r.toNNReal ω) :
    (dividendMeasure D ω) (Set.Ioc s t) =
      ENNReal.ofReal (D t.toNNReal ω - D s.toNNReal ω) := by
  unfold dividendMeasure
  simp only [dif_pos hm]
  rw [StieltjesFunction.measure_Ioc]
  rw [Monotone.stieltjesFunction_eq hm t,
    Monotone.stieltjesFunction_eq hm s, hr t, hr s]
