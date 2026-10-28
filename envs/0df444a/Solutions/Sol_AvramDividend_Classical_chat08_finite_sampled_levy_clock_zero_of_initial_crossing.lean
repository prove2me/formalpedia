-- Prove2me | solution 1 for AvramDividend.Classical.chat08_finite_sampled_levy_clock_zero_of_initial_crossing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T11:27:53.060153+00:00
-- url     : https://prove2.me/submissions/56770fb6-a312-4ef2-bfd1-79711bccdad2

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P ℱ)
    (h : ℝ≥0) (a : ℝ) (n : ℕ) (hn : 0 < n) (ω : Ω)
    (hinit : a < X.X (0 * h) ω) :
    (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
      (fun _ : Ω => (⊤ : WithTop ℝ≥0))
      (fun j σ ω =>
        min (if a < X.X ((j : ℝ≥0) * h) ω
          then (((j : ℝ≥0) * h) : WithTop ℝ≥0) else ⊤)
          (σ ω)) n) ω = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  induction m with
  | zero =>
    show min _ _ = _
    simp only [Nat.cast_zero] at *
    rw [if_pos hinit]; simp only [WithTop.coe_zero, zero_mul]; exact min_eq_left bot_le
  | succ k ih =>
    show min _ _ = _
    rw [ih (by omega)]
    exact min_eq_right bot_le
