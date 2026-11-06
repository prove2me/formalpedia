-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_h_gaussian_original_largeband_mark_integrable_of_ae_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:35:11.493833+00:00
-- url     : https://prove2.me/submissions/63334101-cab1-4a01-98b4-1f531b44d09d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_separated_negative_band_count_finite_every_path
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- On X's original space, a genuine tail-mark bound plus the already-Proved
finite intrinsic large-band count proves signed tail integrability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) :
    let j : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    let N : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j u ≠ 0}).map
        (fun u : ℝ≥0 => (u, j u)))
    let E : Set (ℝ≥0 × ℝ) := Ioc (0 : ℝ≥0) T ×ˢ Iic (-1 : ℝ)
    ∀ C : ℝ, (∀ᵐ p ∂(N.restrict E), ‖p.2‖ ≤ C) →
      IntegrableOn (fun p : ℝ≥0 × ℝ => p.2) E N := by
  intro j N E C hBound
  have hFinite : N E < ⊤ := by
    simpa only [N, E, j, Nat.cast_zero, zero_add, div_one] using
      (avram_wave7_06_original_separated_negative_band_count_finite_every_path
        X ω T 0)
  haveI : IsFiniteMeasure (N.restrict E) :=
    isFiniteMeasure_restrict.mpr (ne_of_lt hFinite)
  have hSm : AEStronglyMeasurable (fun p : ℝ≥0 × ℝ => p.2)
      (N.restrict E) := measurable_snd.aestronglyMeasurable
  exact Integrable.of_bound hSm C hBound
