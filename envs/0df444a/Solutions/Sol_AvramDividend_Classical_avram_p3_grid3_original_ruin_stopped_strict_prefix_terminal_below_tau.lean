-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_strict_prefix_terminal_below_tau
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:11:29.260788+00:00
-- url     : https://prove2.me/submissions/3e7d6ed8-a101-4543-883b-3c71ea29dd2a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_strict_end_cells_form_prefix
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (m : ℕ) (ω : Ω) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    ∃ k : ℕ, k ≤ m + 1 ∧
      (Finset.range (m + 1)).filter
        (fun i => u (i + 1) < τ) = Finset.range k ∧
      (0 < τ → u k < τ) := by
  classical
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun j =>
    min (((min j (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1))) τ
  change ∃ k : ℕ, k ≤ m + 1 ∧
    (Finset.range (m + 1)).filter
      (fun i => u (i + 1) < τ) = Finset.range k ∧
    (0 < τ → u k < τ)
  obtain ⟨k, hkle, hfilter⟩ :=
    avram_p3_grid3_original_ruin_stopped_strict_end_cells_form_prefix
      X x D T m ω
  refine ⟨k, hkle, hfilter, ?_⟩
  intro hτ
  by_cases hk : k = 0
  · subst k
    have hu0 : u 0 = 0 :=
      (avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
        X x D T m ω).1
    simpa only [hu0] using hτ
  · have hklow : 0 < k := Nat.pos_of_ne_zero hk
    have hPrev : k - 1 < k := by omega
    have hmem : k - 1 ∈ (Finset.range (m + 1)).filter
        (fun i => u (i + 1) < τ) := by
      rw [hfilter]
      simpa only [Finset.mem_range] using hPrev
    have hEnd : u (k - 1 + 1) < τ :=
      (Finset.mem_filter.mp hmem).2
    have hidx : k - 1 + 1 = k := by omega
    simpa only [hidx] using hEnd
