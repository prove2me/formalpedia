-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f2_original_frozen_X_cell_exact_Y_J_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T21:50:06.119271+00:00
-- url     : https://prove2.me/submissions/b76d5c62-0ca3-409f-ac77-42d6e5c02164

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The original frozen-X cell is exactly the Y cell plus the physical J jump cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ) :
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
    let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
    let z : ℕ → ℝ := fun i =>
      x + X.X (u i) ω - rightLimit D (u i) ω
    let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
    let j : ℕ → ℝ := fun i => J (u (i + 1)) - J (u i)
    ∀ i, i < n →
      w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
        w (x + X.X (u i) ω - rightLimit D (u i) ω) =
      (w (z i + c i - j i) - w (z i - j i)) +
      (w (z i - j i) - w (z i)) := by
  intro J Y z c j i hi
  have hstart :
      z i = x + X.X (u i) ω - rightLimit D (u i) ω := rfl
  have hend :
      z i + c i - j i =
        x + X.X (u (i + 1)) ω - rightLimit D (u i) ω := by
    dsimp [z, c, j, Y]
    ring
  calc
    w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
        w (x + X.X (u i) ω - rightLimit D (u i) ω) =
        w (z i + c i - j i) - w (z i) := by
          rw [hend, hstart]
    _ = (w (z i + c i - j i) - w (z i - j i)) +
        (w (z i - j i) - w (z i)) := by ring
