-- Prove2me | solution 1 for AvramDividend.Classical.avram_b181_original_random_grid_genuine_marked_source_card_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:18:31.748507+00:00
-- url     : https://prove2.me/submissions/eab2928a-cdee-4c97-a36e-704b1d2d9766

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b180_original_random_grid_any_negative_cutoff_occupied_card_measurable
import Theorems.Thm_AvramDividend_Classical_avram_b125_original_all_zero_poisson_cutoff_counts_imply_true_jumpfree
import Theorems.Thm_AvramDividend_Classical_avram_b179_original_actual_negative_band_source_jump_iff_poisson_count_nonzero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine original source-marked finite random grid count is measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (hs : ∀ i, Measurable (s i)) (ht : ∀ i, Measurable (t i))
    (hOrder : ∀ ω i, s i ω ≤ t i ω) :
    let J : Ω → Finset ℕ := fun ω => by
      classical
      exact S.filter (fun i => ∃ u : ℝ≥0, s i ω < u ∧ u ≤ t i ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
    Measurable (fun ω => ((J ω).card : ℝ)) := by
  intro J
  classical
  let N : ℕ → ℕ → Ω → ℝ≥0∞ := fun cut i ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s i ω) (t i ω) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
  have hEq (ω : Ω) (i : ℕ) :
      (∃ u : ℝ≥0, s i ω < u ∧ u ≤ t i ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ↔
      (∃ cut : ℕ, N cut i ω ≠ 0) := by
    constructor
    · rintro ⟨u, hsu, hut, hne⟩
      by_contra hNo
      have hZero : ∀ cut : ℕ, N cut i ω = 0 := by
        intro cut
        by_contra hc
        exact hNo ⟨cut, hc⟩
      have hJumpfree :=
        avram_b125_original_all_zero_poisson_cutoff_counts_imply_true_jumpfree
          X ω (s i ω) (t i ω) (hOrder ω i)
          (by simpa only [N] using hZero)
      exact hne (hJumpfree u hsu hut)
    · rintro ⟨cut, hcount⟩
      have hCountExact :
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 => (u,
                X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc (s i ω) (t i ω) ×ˢ Iic (-(1 / ((cut : ℝ) + 1)))) ≠ 0 := by
        simpa only [N] using hcount
      obtain ⟨u, hsu, hut, hband⟩ :=
        (avram_b179_original_actual_negative_band_source_jump_iff_poisson_count_nonzero
          X ω (s i ω) (t i ω) (hOrder ω i) cut).mp hCountExact
      have hp : (0 : ℝ) < 1 / ((cut : ℝ) + 1) := by positivity
      have hneg : X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0 :=
        lt_of_le_of_lt hband (neg_lt_zero.mpr hp)
      exact ⟨u, hsu, hut, ne_of_lt hneg⟩
  have hSelector (ω : Ω) :
      S.filter (fun i => ∃ u : ℝ≥0, s i ω < u ∧ u ≤ t i ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) =
      S.filter (fun i => ∃ cut : ℕ, N cut i ω ≠ 0) := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hi, hu⟩
      exact ⟨hi, (hEq ω i).mp hu⟩
    · rintro ⟨hi, hc⟩
      exact ⟨hi, (hEq ω i).mpr hc⟩
  have hM : Measurable (fun ω =>
      ((S.filter (fun i => ∃ cut : ℕ, N cut i ω ≠ 0)).card : ℝ)) := by
    exact avram_b180_original_random_grid_any_negative_cutoff_occupied_card_measurable
      X S s t hs ht
  convert hM using 1
  funext ω
  exact congrArg (fun Q : Finset ℕ => (Q.card : ℝ)) (hSelector ω)
