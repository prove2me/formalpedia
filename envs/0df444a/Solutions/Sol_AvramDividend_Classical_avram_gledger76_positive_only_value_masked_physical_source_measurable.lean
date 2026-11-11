-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger76_positive_only_value_masked_physical_source_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T02:00:30.42679+00:00
-- url     : https://prove2.me/submissions/2b7d25b0-3350-4394-949e-5c0ea1ad2792

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

/-- Inactive cells cancel, so positive-reserve continuity alone suffices
    to make the exact finite physical source sum measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (w : ℝ → ℝ) (hw : ContinuousOn w (Set.Ioi (0 : ℝ)))
    (m : ℕ) (E Y Z : ℕ → Ω → ℝ)
    (hE : ∀ i, Measurable (E i))
    (hY : ∀ i, Measurable (Y i))
    (hZ : ∀ i, Measurable (Z i))
    (hcell : ∀ᵐ ω ∂P, ∀ i ∈ Finset.range (m + 1),
      (E (i + 1) ω = E i ω ∧ Z i ω = Y i ω) ∨
      (0 < Y i ω ∧ 0 < Z i ω)) :
    AEStronglyMeasurable (fun ω =>
      Finset.sum (Finset.range (m + 1)) (fun i =>
        (E (i + 1) ω - E i ω) * w (Y i ω) +
        E (i + 1) ω * (w (Z i ω) - w (Y i ω)))) P := by
  classical
  let wp : ℝ → ℝ := (Ioi (0 : ℝ)).piecewise w (fun _ => 0)
  have hwp : Measurable wp :=
    hw.measurable_piecewise continuousOn_const isOpen_Ioi.measurableSet
  have hterm (i : ℕ) : Measurable (fun ω =>
      (E (i + 1) ω - E i ω) * wp (Y i ω) +
      E (i + 1) ω * (wp (Z i ω) - wp (Y i ω))) :=
    (((hE (i + 1)).sub (hE i)).mul (hwp.comp (hY i))).add
      ((hE (i + 1)).mul ((hwp.comp (hZ i)).sub (hwp.comp (hY i))))
  have hsum : Measurable (fun ω =>
      Finset.sum (Finset.range (m + 1)) (fun i =>
        (E (i + 1) ω - E i ω) * wp (Y i ω) +
        E (i + 1) ω * (wp (Z i ω) - wp (Y i ω)))) := by
    exact Finset.measurable_sum _ (fun i _ => hterm i)
  have heq : (fun ω =>
      Finset.sum (Finset.range (m + 1)) (fun i =>
        (E (i + 1) ω - E i ω) * w (Y i ω) +
        E (i + 1) ω * (w (Z i ω) - w (Y i ω)))) =ᵐ[P]
      (fun ω => Finset.sum (Finset.range (m + 1)) (fun i =>
        (E (i + 1) ω - E i ω) * wp (Y i ω) +
        E (i + 1) ω * (wp (Z i ω) - wp (Y i ω)))) := by
    filter_upwards [hcell] with ω hω
    apply Finset.sum_congr rfl
    intro i hi
    rcases hω i hi with ⟨hfreeze, hsame⟩ | ⟨hypos, hzpos⟩
    · simp [hfreeze, hsame]
    · have hy : wp (Y i ω) = w (Y i ω) := by
        simp [wp, Set.piecewise, hypos]
      have hz : wp (Z i ω) = w (Z i ω) := by
        simp [wp, Set.piecewise, hzpos]
      rw [hy, hz]
  exact hsum.aestronglyMeasurable.congr heq.symm
