-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f2_original_negative_band_ncard_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T01:04:30.554773+00:00
-- url     : https://prove2.me/submissions/796b9e73-e963-4b9c-9af9-015e36c128a2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_intrinsic_marked_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The literal finite-band original path count is Nat-valued measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    Measurable (fun ω : Ω =>
      ({u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard : ℕ)) := by
  classical
  let K : Ω → ℕ := fun ω =>
    {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
  change Measurable K
  have hNm : Measurable N := by
    exact avram_p2_e_compensator_original_intrinsic_marked_count_measurable
      X 0 T (show (0 : ℝ≥0) ≤ T from zero_le) _ measurableSet_Iic
  have hNK (ω : Ω) : N ω = (K ω : ℝ≥0∞) := by
    exact avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card X ω T n
  intro s hs
  have hpre :
      K ⁻¹' s =
        ⋃ k : ℕ, if k ∈ s then N ⁻¹' ({(k : ℝ≥0∞)} : Set ℝ≥0∞) else ∅ := by
    ext ω
    constructor
    · intro hw
      change K ω ∈ s at hw
      apply Set.mem_iUnion.mpr
      refine ⟨K ω, ?_⟩
      simp [hw, hNK ω]
    · intro hw
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hw
      by_cases hks : k ∈ s
      · have hcast : (K ω : ℝ≥0∞) = (k : ℝ≥0∞) := by
          simpa [hks, hNK ω] using hk
        have hnat : K ω = k := by
          exact_mod_cast hcast
        change K ω ∈ s
        simpa [hnat] using hks
      · simpa [hks] using hk
  rw [hpre]
  exact MeasurableSet.iUnion (fun k => by
    by_cases hks : k ∈ s
    · simpa [hks] using hNm (measurableSet_singleton (k : ℝ≥0∞))
    · simp [hks])
