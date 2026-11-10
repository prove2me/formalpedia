-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_phys18_original_discounted_physical_mesh_terminal_source_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T19:04:55.68081+00:00
-- url     : https://prove2.me/submissions/ba34b1e8-2ca9-46b2-8723-3be246124248

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_phys17_original_discounted_reserve_cell_reward_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (n : ℕ),
      let U : ℝ≥0 → ℝ := fun v => x + X.X v ω - rightLimit D v ω
      let J : ℝ≥0 → ℝ := fun r =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ r then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      Real.exp (-(q * (u n : ℝ))) * w (U (u n)) -
        Real.exp (-(q * (u 0 : ℝ))) * w (U (u 0)) =
      ∑ i ∈ Finset.range n,
        (Real.exp (-(q * (u (i + 1) : ℝ))) *
          (w (U (u i) +
            (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift -
              (J (u (i + 1)) - J (u i)) -
              (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω))) -
           w (U (u i))) +
         (Real.exp (-(q * (u (i + 1) : ℝ))) -
          Real.exp (-(q * (u i : ℝ)))) * w (U (u i))) := by
  filter_upwards [
    avram_bv_phys17_original_discounted_reserve_cell_reward_ae X hX hBV q w x D
  ] with ω hcell
  intro u n
  dsimp only
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hs := hcell (u n) (u (n + 1))
      dsimp only at hs
      linear_combination ih + hs
