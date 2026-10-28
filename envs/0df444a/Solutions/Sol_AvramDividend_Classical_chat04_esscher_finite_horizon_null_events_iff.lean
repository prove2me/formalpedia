-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_finite_horizon_null_events_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:19:03.200797+00:00
-- url     : https://prove2.me/submissions/93806b04-4a17-4b65-af6a-79478cfcd2d2

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Process.Adapted
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0)
    (θ : ℝ) (A : Set Ω) :
    (P.withDensity (fun ω : Ω =>
      ENNReal.ofReal (Real.exp
        (θ * X.X t ω - (t : ℝ) * X.ψ θ)))) A = 0 ↔ P A = 0 := by
  have hmX : Measurable (X.X t) := X.adapted.measurable
  have hmReal : Measurable (fun ω : Ω =>
      Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ)) :=
    Real.continuous_exp.measurable.comp
      ((measurable_const.mul hmX).sub measurable_const)
  have hmF : Measurable (fun ω : Ω =>
      ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ))) :=
    ENNReal.measurable_ofReal.comp hmReal
  have hset : {ω : Ω |
      ENNReal.ofReal
        (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ)) ≠ 0} = Set.univ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact ne_of_gt ((ENNReal.ofReal_pos).2 (Real.exp_pos _))
  simpa only [hset, Set.univ_inter] using
    (withDensity_apply_eq_zero
      (μ := P) (f := fun ω : Ω =>
        ENNReal.ofReal
          (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ)))
      (s := A) hmF)
