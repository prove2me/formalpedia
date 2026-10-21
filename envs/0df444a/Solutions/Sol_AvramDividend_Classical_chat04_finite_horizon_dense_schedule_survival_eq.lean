-- Prove2me | solution 1 for AvramDividend.Classical.chat04_finite_horizon_dense_schedule_survival_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T10:11:14.640163+00:00
-- url     : https://prove2.me/submissions/82b69829-5c99-4ab8-b7c4-432ec15edfce

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_lower_before_horizon_countable_grid_iff
import Theorems.Thm_AvramDividend_Classical_chat03_upper_before_horizon_countable_grid_iff
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
A countable schedule covering every reciprocal-natural grid detects every
strict exit BEFORE a finite horizon, with the correct open endpoint t<T.
This is the genuine finite-horizon survival event needed for killed kernels.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (lower upper : ℝ) (T : ℝ≥0) :
    {ω | ∀ t : ℝ≥0, t < T →
      ¬ (X.X t ω < lower ∨ upper < X.X t ω)} =
      ⋂ j : ℕ, {ω | τ j < T →
        ¬ (X.X (τ j) ω < lower ∨ upper < X.X (τ j) ω)} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iInter]
  constructor
  · intro h j hj
    exact h (τ j) hj
  · intro h t htT hbad
    rcases hbad with hLower | hUpper
    · obtain ⟨n, hn, k, hkT, hkLower⟩ :=
        (AvramDividend.Classical.chat03_lower_before_horizon_countable_grid_iff
          X ω lower T).mp ⟨t, htT, hLower⟩
      obtain ⟨j, hj⟩ := hCover n hn k
      have hτT : τ j < T := by simpa only [hj] using hkT
      have hcontr := h j hτT
      apply hcontr
      left
      simpa only [hj] using hkLower
    · obtain ⟨n, hn, k, hkT, hkUpper⟩ :=
        (AvramDividend.Classical.chat03_upper_before_horizon_countable_grid_iff
          X ω upper T).mp ⟨t, htT, hUpper⟩
      obtain ⟨j, hj⟩ := hCover n hn k
      have hτT : τ j < T := by simpa only [hj] using hkT
      have hcontr := h j hτT
      apply hcontr
      right
      simpa only [hj] using hkUpper
