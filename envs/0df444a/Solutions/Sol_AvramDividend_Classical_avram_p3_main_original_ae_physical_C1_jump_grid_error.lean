-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_main_original_ae_physical_C1_jump_grid_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:30:11.697902+00:00
-- url     : https://prove2.me/submissions/463fa1af-4ed6-4f65-b53d-60e04a161bde

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_jump_removed_grid_variation
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_finite_grid_C1_two_stage_error
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Almost surely on actual original BV Lévy paths, the exact physical
C1 plus intrinsic negative-jump two-stage mesh error obeys a true
drift-minus-nonzero-residual variation envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (n : ℕ) (u : ℕ → ℝ≥0)
    (hGrid : ∀ i, i < n → u i ≤ u (i + 1))
    (S : Finset ℕ) (w : ℝ → ℝ) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0)
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
      let j : ℕ → ℝ := fun i => J (u (i + 1)) - J (u i)
      let d : ℕ → ℝ := fun i => X.X (u (i + 1)) ω - X.X (u i) ω
      let B : ℝ := |X.drift| * ((u n : ℝ) - (u 0 : ℝ)) +
        (R (u n) - R (u 0))
      ∀ (r z : ℕ → ℝ) (ε K : ℝ)
        (hε : 0 ≤ ε) (hK : 0 ≤ K)
        (hr : ∀ i, i < n → 0 ≤ r i ∧ r i ≤ 1)
        (htaylor : ∀ i, i < n →
          |w (z i + c i) - w (z i) - deriv w (z i) * c i| ≤
            ε * |c i|)
        (hlarge : ∀ i, i < n → i ∈ S →
          |w (z i + c i - j i) - w (z i - j i)| ≤ K * |c i| ∧
          |w (z i + c i) - w (z i)| ≤ K * |c i|)
        (hsmall : ∀ i, i < n → i ∉ S →
          |w (z i + c i - j i) - w (z i + c i)| ≤ K * |j i| ∧
          |w (z i - j i) - w (z i)| ≤ K * |j i|),
      |∑ i ∈ Finset.range n,
        r i * ((w (z i + d i) - w (z i)) -
          (w (z i - j i) - w (z i)) -
          deriv w (z i) * c i)| ≤
        ε * B + 2 * K * (∑ i ∈ Finset.range n,
          if i ∈ S then |c i| else |j i|) := by
  filter_upwards
    [avram_p3_main_original_jump_removed_grid_variation X hBV] with ω hω
  intro J R Y c j d B
  intro r z ε K hε hK hr htaylor hlarge hsmall
  have hstep : ∀ i, i < n → d i = c i - j i := by
    intro i hi
    dsimp [d, c, j, Y]
    ring
  have hvar : (∑ i ∈ Finset.range n, |c i|) ≤ B := by
    simpa only [c, B, J, R, Y] using (hω n u hGrid)
  exact avram_p3_main_original_finite_grid_C1_two_stage_error
    n S w r z c j d ε B K hε hK hstep hr htaylor hvar hlarge hsmall
