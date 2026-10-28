-- Prove2me | solution 1 for AvramDividend.Classical.nextRecord_shifted_upclock_finite_of_finite_later_record
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:56:04.433649+00:00
-- url     : https://prove2.me/submissions/fdd09932-43fa-4e97-a413-6b52126dcc87

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_eq_add_shifted_inf
import Mathlib.Data.ENNReal.Operations
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (b ε : ℝ) (hε : 0 ≤ ε) (u v δ : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b)
    (hv : (v : ℝ≥0∞) = twoSidedExitUpTime X (b + ε) ω)
    (hδ : u + δ = v) :
    (⨅ (t : ℝ≥0)
      (_ : ε < X.X (u + t) ω - X.X u ω), (t : ℝ≥0∞)) ≠ ⊤ := by
  have hclock := nextRecord_upclock_eq_add_shifted_inf
    X b ε hε u ω hu hAt
  have hcoeeq : (u : ℝ≥0∞) + (δ : ℝ≥0∞) =
      (u : ℝ≥0∞) + (⨅ (t : ℝ≥0)
      (_ : ε < X.X (u + t) ω - X.X u ω), (t : ℝ≥0∞)) := by
    calc
      (u : ℝ≥0∞) + (δ : ℝ≥0∞) =
          ((u + δ : ℝ≥0) : ℝ≥0∞) := by simp
      _ = (v : ℝ≥0∞) := by rw [hδ]
      _ = (u : ℝ≥0∞) + (⨅ (t : ℝ≥0)
          (_ : ε < X.X (u + t) ω - X.X u ω), (t : ℝ≥0∞)) :=
        hv.trans hclock
  have hδEq : (δ : ℝ≥0∞) = (⨅ (t : ℝ≥0)
      (_ : ε < X.X (u + t) ω - X.X u ω), (t : ℝ≥0∞)) :=
    (ENNReal.add_right_inj (by simp : (u : ℝ≥0∞) ≠ ⊤)).mp hcoeeq
  rw [← hδEq]
  simp
