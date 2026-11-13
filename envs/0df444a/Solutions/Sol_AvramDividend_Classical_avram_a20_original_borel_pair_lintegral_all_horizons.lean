-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_borel_pair_lintegral_all_horizons
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:40:06.375125+00:00
-- url     : https://prove2.me/submissions/1ff588b6-c3c2-4f32-93a5-8653ce033390

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_chronological_pair_lintegral_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let S : Ω → Set ℝ≥0 := fun ω => {u : ℝ≥0 |
      0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}
    let K : Ω → ℕ := fun ω => ((S ω ×ˢ S ω) ∩
      {p : ℝ≥0 × ℝ≥0 | p.1 < p.2}).ncard
    (∫⁻ ω, (K ω : ℝ≥0∞) ∂P) =
      (((T : ℝ≥0∞) * X.ν B) ^ 2) / 2 := by
  intro S K
  by_cases hT : 0 < T
  · simpa only [S, K] using
      (avram_a20_original_borel_chronological_pair_lintegral_exact
        X hFinite T hT B hB hNeg)
  · have hT0 : T = 0 :=
      le_antisymm (le_of_not_gt hT) zero_le
    subst T
    have hEmpty (ω : Ω) : S ω = ∅ := by
      ext u
      simp only [S, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact (not_lt_of_ge h.2.1) h.1
    simp [K, hEmpty]
