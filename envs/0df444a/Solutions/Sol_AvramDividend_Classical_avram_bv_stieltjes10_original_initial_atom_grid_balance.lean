-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_stieltjes10_original_initial_atom_grid_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:29:03.469905+00:00
-- url     : https://prove2.me/submissions/bc5cc14b-2b7f-493a-9724-f25bbbd0321a

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The first Stieltjes atom is preserved by any finite grid telescope
starting at zero, with no assumptions on mesh refinement. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ)
    (hu0 : u 0 = 0) :
    dividendMeasure D ω {(0 : ℝ)} =
      ENNReal.ofReal
        (rightLimit D (u n) ω - D 0 ω -
          ∑ i ∈ Finset.range n,
            (rightLimit D (u (i + 1)) ω -
              rightLimit D (u i) ω)) := by
  have hgrid (m : ℕ) :
      (∑ i ∈ Finset.range m,
        (rightLimit D (u (i + 1)) ω -
          rightLimit D (u i) ω)) =
      rightLimit D (u m) ω - rightLimit D (u 0) ω := by
    induction m with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  calc
    dividendMeasure D ω {(0 : ℝ)}
        = ENNReal.ofReal (rightLimit D 0 ω - D 0 ω) := by
          simpa using
            (dividendMeasure_singleton_eq_rightLimit_sub D hD ω (0 : ℝ≥0))
    _ = ENNReal.ofReal
          (rightLimit D (u n) ω - D 0 ω -
            ∑ i ∈ Finset.range n,
              (rightLimit D (u (i + 1)) ω -
                rightLimit D (u i) ω)) := by
          rw [hgrid n, hu0]
          congr 1
          ring
