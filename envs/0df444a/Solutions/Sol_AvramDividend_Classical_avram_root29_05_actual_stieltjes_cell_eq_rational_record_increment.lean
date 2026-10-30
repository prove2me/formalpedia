-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_actual_stieltjes_cell_eq_rational_record_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:58:48.471444+00:00
-- url     : https://prove2.me/submissions/7c0c7c54-0b16-42da-beb1-1b8b66320203

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_record_increment
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_cantorSchedule_rationalGrid

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- Exact Stieltjes dividend cash in a rational grid cell equals the
increment of the globally countable Lévy record skeleton. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (n k : ℕ) (hn : 0 < n) :
    let t : ℕ → ℝ≥0 := fun j => (j : ℝ≥0) * (n : ℝ≥0)⁻¹
    let sampledRecord : ℕ → ℝ := fun j =>
      ⨆ s : {s : ℝ≥0 //
        s ∈ Set.range (fun i : ℕ =>
          ((Nat.unpair i).2 : ℝ≥0) *
            (((((Nat.unpair i).1 + 1) : ℕ) : ℝ≥0)⁻¹)) ∧ s ≤ t j},
        X.X s.1 ω
    (dividendMeasure (runningSup X) ω)
      (Set.Ioc (t k : ℝ) (t (k + 1) : ℝ)) =
      ENNReal.ofReal (sampledRecord (k + 1) - sampledRecord k) := by
  dsimp only
  rw [runningSup_dividendMeasure_Ioc_eq_record_increment]
  simp only [Real.toNNReal_coe]
  rw [runningSup_eq_cantorSchedule_rationalGrid X ω n (k + 1) hn]
  rw [runningSup_eq_cantorSchedule_rationalGrid X ω n k hn]
