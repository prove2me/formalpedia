-- Prove2me | solution 1 for ContinuousExpectation.cdfExpectation_integrable_and_eq_integral_pdf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:21:15.242369+00:00
-- url     : https://prove2.me/submissions/b6a36f8a-595e-4207-a657-7940bb4a363a

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F000
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_thm_1_4
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ContinuousExpectation
open Set MeasureTheory
open scoped BigOperators Pointwise Interval
noncomputable section

theorem solution
    {a b : ℝ} {F pdf : ℝ → ℝ}
    (hab : a < b)
    (hFmono : Monotone F)
    (hFderiv : ∀ x ∈ Set.Icc a b, HasDerivAt F (pdf x) x)
    (hpdf_cont : ContinuousOn pdf (Set.Icc a b))
    (h_int : RSIntegrable (fun x => x) F a b) :
    IntervalIntegrable (fun x => x * pdf x) MeasureTheory.volume a b ∧
      cdfExpectation a b F h_int = ∫ x in a..b, x * pdf x := by
  have hid_cont : ContinuousOn (fun x : ℝ => x) (Set.Icc a b) :=
    continuous_id.continuousOn

  have h :
      IntervalIntegrable (fun x => x * pdf x) MeasureTheory.volume a b ∧
        rsIntegral (fun x : ℝ => x) F a b h_int =
          ∫ x in a..b, x * pdf x :=
    thm_1_4
      (f := fun x : ℝ => x)
      (α := F)
      (α' := pdf)
      (a := a)
      (b := b)
      (le_of_lt hab)
      hid_cont
      (hFmono.monotoneOn (Set.Icc a b))
      hFderiv
      hpdf_cont
      h_int

  constructor
  · exact h.1
  · unfold cdfExpectation
    exact h.2
