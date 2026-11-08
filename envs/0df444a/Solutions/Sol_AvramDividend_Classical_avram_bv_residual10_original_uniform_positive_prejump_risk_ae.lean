-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_original_uniform_positive_prejump_risk_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T22:27:41.584066+00:00
-- url     : https://prove2.me/submissions/189abc50-f990-4827-9ded-de06af23efa7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_stieltjes10_original_countable_positive_grid_prejump

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At every strictly positive point on every original uniform grid,
the pre-right dividend reserve equals the actual risk reserve a.s. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i,
      (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ᵐ ω ∂P, ∀ n i : ℕ,
      Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
          (u n (i + 1)) =
        riskProcess X x D (u n (i + 1)) ω := by
  have hpos (n i : ℕ) : 0 < u n (i + 1) := by
    have hi : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_pos i
    have hd : 0 < (n : ℝ) + 2 := by positivity
    have hr : (0 : ℝ) < (u n (i + 1) : ℝ) := by
      rw [huniform n (i + 1)]
      exact div_pos (mul_pos hT hi) hd
    exact_mod_cast hr
  have hrows (n : ℕ) :
      ∀ᵐ ω ∂P, ∀ i : ℕ,
        Function.leftLim
            (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
            (u n (i + 1)) =
          riskProcess X x D (u n (i + 1)) ω := by
    exact avram_bv_stieltjes10_original_countable_positive_grid_prejump
      X x D hD (fun i => u n (i + 1)) (hpos n)
  exact (ae_all_iff).2 hrows
