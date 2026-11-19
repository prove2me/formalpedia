-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_zero_or_strict_canonical_cash_mesh_error_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:31:09.931529+00:00
-- url     : https://prove2.me/submissions/86c66f47-ec6d-4f7d-b1a8-18999d97bfea

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_canonical_clipped_stieltjes_cash_discount_error_zero
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b250_original_ruinclipped_true_physical_stopped_cell_width_and_clock_monotone
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_canonical_grid_reaches_bounded_clock_every_mesh
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (t : ℝ≥0) (n : ℕ) (ht : t ≤ (n : ℝ≥0))
    (hClock : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    let N : ℕ → ℕ := fun j => (n + 1) * (j + 1)
    let v : ℕ → ℕ → ℝ≥0 := fun j i =>
      min ((i : ℝ≥0) * ((1 : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0))) t
    Tendsto (fun j : ℕ =>
      ∑ i ∈ Finset.range (N j),
        ((∫⁻ r in paymentTimes (ruinTime X x D ω) ∩
            Ioc (v j i : ℝ) (v j (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * r)))
            ∂(dividendMeasure D ω)).toReal -
          Real.exp (-(q * (v j (i + 1) : ℝ))) *
            (rightLimit D (v j (i + 1)) ω - rightLimit D (v j i) ω)))
      atTop (𝓝 (0 : ℝ)) := by
  rcases hClock with h0 | hStrict
  · subst t
    simp
  · exact avram_jump6_B_original_canonical_clipped_stieltjes_cash_discount_error_zero
      X x C D hD ω q hq t n ht hStrict
