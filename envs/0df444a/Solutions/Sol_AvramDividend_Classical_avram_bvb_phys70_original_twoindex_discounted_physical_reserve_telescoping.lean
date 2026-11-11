-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys70_original_twoindex_discounted_physical_reserve_telescoping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:22:32.761525+00:00
-- url     : https://prove2.me/submissions/5f7581e9-8f3e-4a39-863b-6e2fd96f40bb

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_phys18_original_discounted_physical_mesh_terminal_source_ae
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Physical discounted reserve telescopes across the original two-index
grid, with the true removed-jump source and right-limit dividends. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      let U : ℝ≥0 → ℝ := fun v => x + X.X v ω - rightLimit D v ω
      let J : ℝ≥0 → ℝ := fun r =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ r then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      Real.exp (-(q * (u n (n + 1) : ℝ))) * w (U (u n (n + 1))) -
        Real.exp (-(q * (u n 0 : ℝ))) * w (U (u n 0)) =
      ∑ i ∈ Finset.range (n + 1),
        (Real.exp (-(q * (u n (i + 1) : ℝ))) *
          (w (U (u n i) +
            (((u n (i + 1) : ℝ) - (u n i : ℝ)) * X.drift -
              (J (u n (i + 1)) - J (u n i)) -
              (rightLimit D (u n (i + 1)) ω - rightLimit D (u n i) ω))) -
           w (U (u n i))) +
         (Real.exp (-(q * (u n (i + 1) : ℝ))) -
          Real.exp (-(q * (u n i : ℝ)))) * w (U (u n i))) := by
  have h := avram_bv_phys18_original_discounted_physical_mesh_terminal_source_ae
    X hX hBV q w x D
  filter_upwards [h] with ω hω
  intro n
  exact hω (u n) (n + 1)
