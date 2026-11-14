-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a116_original_gaussian_clipped_crossing_positive_residual_ae_zero_glue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:39:09.805084+00:00
-- url     : https://prove2.me/submissions/e8507422-8d6d-4e81-9518-d6cbca14edeb

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

/-- The true original Gaussian stopped crossing positive residual vanishes pathwise once the actual stopped source value increment and physical HJB compensation vanish. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E A H : ℕ → Ω → ℝ)
    (hE : ∀ m ω, 0 ≤ E m ω ∧ E m ω ≤ 1)
    (hAt : ∀ᵐ ω ∂P, Tendsto (fun m => A m ω) atTop (𝓝 (0 : ℝ)))
    (hHt : ∀ᵐ ω ∂P, Tendsto (fun m => H m ω) atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂P, Tendsto
      (fun m => max (E m ω * A m ω - H m ω) 0)
      atTop (𝓝 (0 : ℝ)) := by
  filter_upwards [hAt, hHt] with ω hA hH
  have hTotal : Tendsto (fun m => |A m ω| + |H m ω|)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [abs_zero, zero_add] using hA.abs.add hH.abs
  have hPos (m : ℕ) :
      0 ≤ max (E m ω * A m ω - H m ω) 0 :=
    le_max_right _ 0
  have hBound (m : ℕ) :
      max (E m ω * A m ω - H m ω) 0 ≤
        |A m ω| + |H m ω| := by
    obtain ⟨hE0,hE1⟩ := hE m ω
    have hAbsMul : |E m ω * A m ω| ≤ |A m ω| := by
      rw [abs_mul, abs_of_nonneg hE0]
      simpa only [one_mul] using (mul_le_mul_of_nonneg_right hE1 (abs_nonneg (A m ω)))
    apply max_le
    · linarith [le_abs_self (E m ω * A m ω),
        neg_le_abs (H m ω)]
    · linarith [abs_nonneg (A m ω), abs_nonneg (H m ω)]
  exact squeeze_zero hPos hBound hTotal
