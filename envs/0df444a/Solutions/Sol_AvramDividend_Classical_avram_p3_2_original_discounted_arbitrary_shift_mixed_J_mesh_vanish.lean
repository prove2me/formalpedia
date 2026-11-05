-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_discounted_arbitrary_shift_mixed_J_mesh_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:25:03.789215+00:00
-- url     : https://prove2.me/submissions/6d28f15d-279e-41f0-8a31-f0a481dfeea1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_drift_mixed_commutator_J_variation_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Genuine BV discounted mixed raw-J errors vanish for any shrinking
physical drift-shift sequence, with the actual finite jump variation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
      ∀ (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ)
        (z c : ℕ → ℕ → ℝ),
        let j : ℕ → ℕ → ℝ := fun m i =>
          J (u m (i + 1)) - J (u m i)
        (∀ m, u m 0 = 0) →
        (∀ m, u m (n m) = T) →
        (∀ m i, i < n m → u m i ≤ u m (i + 1)) →
        (∀ ε : ℝ, 0 < ε →
          ∀ᶠ m in Filter.atTop, ∀ i, i < n m →
            |w (z m i + c m i - j m i) - w (z m i + c m i) -
              w (z m i - j m i) + w (z m i)| ≤ ε * |j m i|) →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ m in Filter.atTop,
            |∑ i ∈ Finset.range (n m),
              Real.exp (-(q * (u m i : ℝ))) *
                (w (z m i + c m i - j m i) - w (z m i + c m i) -
                  w (z m i - j m i) + w (z m i))| < η := by
  filter_upwards
    [avram_p3_2_original_drift_mixed_commutator_J_variation_bound X hBV w q hq]
    with ω hBound
  intro J T u n z c j hStart hEnd hGrid hCellEventually η hη
  let M : ℝ := J T - J 0
  let B : ℝ := |M| + 1
  have hB : 0 < B := by
    dsimp [B]
    linarith [abs_nonneg M]
  have hε : 0 < η / B := div_pos hη hB
  filter_upwards [hCellEventually (η / B) hε] with m hCell
  have hEstimate :=
    hBound (u m) (n m) (hGrid m) (z m) (c m)
      (η / B) (le_of_lt hε) (by
        intro i hi
        exact hCell i hi)
  have hClock : J (u m (n m)) - J (u m 0) = M := by
    simp only [hStart m, hEnd m]
    rfl
  have hMB : M < B := by
    dsimp [B]
    linarith [le_abs_self M]
  calc
    |∑ i ∈ Finset.range (n m),
      Real.exp (-(q * (u m i : ℝ))) *
        (w (z m i + c m i - j m i) - w (z m i + c m i) -
          w (z m i - j m i) + w (z m i))| ≤
      (η / B) * (J (u m (n m)) - J (u m 0)) := hEstimate
    _ = (η / B) * M := by rw [hClock]
    _ < (η / B) * B := mul_lt_mul_of_pos_left hMB hε
    _ = η := by field_simp [ne_of_gt hB]
