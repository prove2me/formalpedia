-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_strict_end_cells_form_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:05:18.135623+00:00
-- url     : https://prove2.me/submissions/4681c40d-e2cf-4f57-8aae-18ee8e9b89ad

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
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
        (fun i => u (i + 1) < τ) = Finset.range k := by
  classical
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun j =>
    min (((min j (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1))) τ
  change ∃ k : ℕ, k ≤ m + 1 ∧
    (Finset.range (m + 1)).filter
      (fun i => u (i + 1) < τ) = Finset.range k
  have hu : Monotone u :=
    (avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
      X x D T m ω).2.2
  have haux : ∀ n : ℕ, ∃ k : ℕ, k ≤ n ∧
      ∀ i : ℕ, i < n → (u (i + 1) < τ ↔ i < k) := by
    intro n
    induction n with
    | zero =>
        refine ⟨0, by omega, ?_⟩
        intro i hi
        omega
    | succ n ih =>
        by_cases hn : u (n + 1) < τ
        · refine ⟨n + 1, by omega, ?_⟩
          intro i hi
          constructor
          · intro _
            omega
          · intro _
            have hle : i + 1 ≤ n + 1 := by omega
            exact lt_of_le_of_lt (hu hle) hn
        · rcases ih with ⟨k, hk, hiff⟩
          refine ⟨k, by omega, ?_⟩
          intro i hi
          by_cases hin : i < n
          · exact hiff i hin
          · have hieq : i = n := by omega
            subst i
            simp [hn, Nat.not_lt_of_ge hk]
  rcases haux (m + 1) with ⟨k, hk, hiff⟩
  refine ⟨k, hk, ?_⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro hi
    exact (hiff i hi.1).mp hi.2
  · intro hik
    have him : i < m + 1 := lt_of_lt_of_le hik hk
    exact ⟨him, (hiff i him).mpr hik⟩
