-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_endpoint_left_jump_tsum_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:15:14.888665+00:00
-- url     : https://prove2.me/submissions/5bf8dd8a-253c-404e-ba80-2f358826dd2c

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The complete actual negative left-jump magnitude sum up to a positive
time splits into the genuine jump at that time and all earlier jumps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    (∑' (u : ℝ≥0),
      if 0 < u ∧ u ≤ t then
        ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
      else 0) =
      ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) t - X.X t ω) +
      (∑' (u : ℝ≥0),
        if 0 < u ∧ u < t then
          ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        else 0) := by
  classical
  let J : ℝ≥0 → ℝ≥0∞ := fun u =>
    ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
  change (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then J u else 0) =
    J t + (∑' u : ℝ≥0, if 0 < u ∧ u < t then J u else 0)
  rw [ENNReal.tsum_eq_add_tsum_ite t]
  simp only [ht, le_refl, and_self, ↓reduceIte]
  congr 1
  apply tsum_congr
  intro u
  by_cases heq : u = t
  · subst u
    simp
  · by_cases hlt : 0 < u ∧ u < t
    · have hle : 0 < u ∧ u ≤ t := ⟨hlt.1, le_of_lt hlt.2⟩
      simp [heq, hlt, hle]
    · by_cases hle : 0 < u ∧ u ≤ t
      · have hstrict : u < t := lt_of_le_of_ne hle.2 heq
        exact False.elim (hlt ⟨hle.1, hstrict⟩)
      · simp [heq, hlt, hle]
