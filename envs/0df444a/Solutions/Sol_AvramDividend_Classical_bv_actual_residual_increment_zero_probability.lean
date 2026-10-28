-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_residual_increment_zero_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:37:01.496588+00:00
-- url     : https://prove2.me/submissions/49857e4c-ea4a-424b-a635-befe56fde6ec

import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_zero_atom_survival
import Mathlib.Probability.IdentDistrib
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal

/-- The actual drift residual has exponentially distributed zero-increment survival on any fixed interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t) :
    P.real {ω : Ω |
      ((t : ℝ) * X.drift - X.X t ω) -
        ((s : ℝ) * X.drift - X.X s ω) = 0} =
      Real.exp (-(((t - s : ℝ≥0) : ℝ) *
        (X.ν (Iio (0 : ℝ))).toReal)) := by
  let Δ : ℝ≥0 := t - s
  let a : ℝ := (Δ : ℝ) * X.drift
  have hcoe : (Δ : ℝ) = (t : ℝ) - (s : ℝ) :=
    NNReal.coe_sub hst
  have hset :
      {ω : Ω |
        ((t : ℝ) * X.drift - X.X t ω) -
          ((s : ℝ) * X.drift - X.X s ω) = 0} =
      {ω : Ω | X.X t ω - X.X s ω = a} := by
    ext ω
    change (((t : ℝ) * X.drift - X.X t ω) -
        ((s : ℝ) * X.drift - X.X s ω) = 0) ↔
        (X.X t ω - X.X s ω = a)
    dsimp [a]
    rw [hcoe]
    constructor <;> intro h <;> nlinarith
  have hmeasure :
      P {ω : Ω | X.X t ω - X.X s ω = a} =
      P {ω : Ω | X.X Δ ω = a} := by
    have heq := (X.stationaryIncrements s t hst).measure_mem_eq
      (s := {a}) (measurableSet_singleton a)
    simpa only [Set.preimage, Set.mem_singleton_iff] using heq
  have hbase :
      {ω : Ω | X.X Δ ω = a} =
      {ω : Ω | (Δ : ℝ) * X.drift - X.X Δ ω = 0} := by
    ext ω
    change (X.X Δ ω = a) ↔ ((Δ : ℝ) * X.drift - X.X Δ ω = 0)
    dsimp [a]
    constructor <;> intro h <;> linarith
  rw [hset]
  have hreal : P.real {ω : Ω | X.X t ω - X.X s ω = a} =
      P.real {ω : Ω | X.X Δ ω = a} := by
    simp only [Measure.real]
    exact congrArg ENNReal.toReal hmeasure
  rw [hreal, hbase]
  exact bv_actual_residual_zero_atom_survival X hBV hFinite Δ
