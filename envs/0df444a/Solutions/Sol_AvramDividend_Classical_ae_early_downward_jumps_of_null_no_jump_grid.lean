-- Prove2me | solution 1 for AvramDividend.Classical.ae_early_downward_jumps_of_null_no_jump_grid
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:06:16.183736+00:00
-- url     : https://prove2.me/submissions/be3dc32f-cff1-4756-a84c-875c3e66e680

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Data.NNReal.Basic

open MeasureTheory Set Filter
open scoped NNReal
open AvramDividend.Classical

/-- A countable null no-jump grid gives almost-sure downward jumps arbitrarily near zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (δ : ℕ → ℝ≥0)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε → ∃ n : ℕ, δ n < ε)
    (hnull : ∀ n : ℕ,
      P {ω : Ω | ¬ ∃ t : ℝ≥0, 0 < t ∧ t < δ n ∧
        ∃ l : ℝ,
          Tendsto (fun s : ℝ≥0 => X.X s ω)
            (nhdsWithin t (Iio t)) (nhds l) ∧ X.X t ω < l} = 0) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, 0 < t ∧ t < ε ∧
        ∃ l : ℝ,
          Tendsto (fun s : ℝ≥0 => X.X s ω)
            (nhdsWithin t (Iio t)) (nhds l) ∧ X.X t ω < l := by 
  have h : ∀ n : ℕ, ∀ᵐ ω ∂P, ∃ t : ℝ≥0, 0 < t ∧ t < δ n ∧
        ∃ l : ℝ,
          Tendsto (fun s : ℝ≥0 => X.X s ω)
            (nhdsWithin t (Iio t)) (nhds l) ∧ X.X t ω < l := fun n =>
    measure_eq_zero_iff_ae_notMem.1 (hnull n) |>.mono fun ω hω => by simpa using hω
  filter_upwards [ae_all_iff.2 h] with ω hω ε hε
  obtain ⟨n, hn⟩ := hcofinal ε hε
  obtain ⟨t, ht0, htn, l, hl⟩ := hω n
  exact ⟨t, ht0, htn.trans hn, l, hl⟩
