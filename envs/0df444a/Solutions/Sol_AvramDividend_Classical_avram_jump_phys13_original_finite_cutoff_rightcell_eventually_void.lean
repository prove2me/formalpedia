-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump_phys13_original_finite_cutoff_rightcell_eventually_void
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T01:06:00.676814+00:00
-- url     : https://prove2.me/submissions/b6b4e3f3-7b47-4229-b8bc-71e00a9ae1ff

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A finite original negative-jump band contributes no post-stop jumps in shrinking final cells. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (cut : ℕ) (τ : ℝ≥0)
    (e : ℕ → ℝ≥0) (heBound : ∀ k, e k ≤ T)
    (heTendsto : Tendsto e atTop (𝓝 τ)) :
    ∀ᶠ k in atTop,
      {u : ℝ≥0 | τ < u ∧ u ≤ e k ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((cut : ℝ) + 1))} = ∅ := by
  classical
  let S : Set ℝ≥0 := {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
      -(1 / ((cut : ℝ) + 1))}
  have hS : S.Finite :=
    avram_wave7_06_original_negative_band_marked_times_finite X ω T cut
  have hAvoid : ∀ᶠ k in atTop, ∀ u ∈ S, u ≤ τ ∨ e k < u := by
    apply hS.eventually_all.mpr
    intro u hu
    by_cases h : u ≤ τ
    · exact Filter.Eventually.of_forall (fun _ => Or.inl h)
    · have hτu : τ < u := lt_of_not_ge h
      filter_upwards [heTendsto.eventually (Iio_mem_nhds hτu)] with k hk
      exact Or.inr hk
  filter_upwards [hAvoid] with k hk
  ext u
  constructor
  · intro hu
    change τ < u ∧ u ≤ e k ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((cut : ℝ) + 1)) at hu
    obtain ⟨hτu, hue, huz⟩ := hu
    have huS : u ∈ S :=
      ⟨lt_of_le_of_lt (show (0 : ℝ≥0) ≤ τ from zero_le) hτu,
       le_trans hue (heBound k), huz⟩
    rcases hk u huS with hle | hlt
    · exact False.elim ((not_lt_of_ge hle) hτu)
    · exact False.elim ((not_le_of_gt hlt) hue)
  · intro hu
    simp at hu
