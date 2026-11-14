-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb23_original_zero_reserve_uniform_grid_generator_rest_cells_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:09:18.949119+00:00
-- url     : https://prove2.me/submissions/c091c984-2f34-449b-b1aa-70a19f94e77c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (q : ℝ)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ) (ω : Ω) (S : ℝ≥0)
    (hBound : ∀ i, i ≤ n + 1 → u n i ≤ S)
    (hPre : ∀ i : ℕ,
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
        (u n (i + 1)) =
      riskProcess X x D (u n (i + 1)) ω)
    (hZero : ∀ t : ℝ≥0, t ≤ S → riskProcess X x D t ω = 0) :
    let Z : ℕ → ℝ := fun i => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    let G : ℕ → ℝ := fun i =>
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w (Z i) - q * w (Z i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
    (∑ i ∈ Finset.range (n + 1), G i) = G 0  := by
  dsimp
  apply Finset.sum_eq_single 0
  · intro i hi hne
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hne
    have hIndex : j + 1 ≤ n + 1 := by
      exact Nat.le_of_lt (Finset.mem_range.mp hi)
    have hZzero :
        Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
          (u n (j + 1)) = 0 := by
      calc
        _ = riskProcess X x D (u n (j + 1)) ω := hPre j
        _ = 0 := hZero _ (hBound (j + 1) hIndex)
    simp [hZzero]
  · intro h0
    exact False.elim (h0 (by simp))
