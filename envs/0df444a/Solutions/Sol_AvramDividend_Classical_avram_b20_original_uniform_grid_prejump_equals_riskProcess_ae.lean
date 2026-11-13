-- Prove2me | solution 1 for AvramDividend.Classical.avram_b20_original_uniform_grid_prejump_equals_riskProcess_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T09:06:38.486204+00:00
-- url     : https://prove2.me/submissions/db1343aa-0181-43ea-9312-e1c02b34464e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_stieltjes10_original_countable_positive_grid_prejump
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ᵐ ω ∂P, ∀ n i,
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
        (u n (i + 1)) =
      riskProcess X x D (u n (i + 1)) ω := by
  classical
  apply ae_all_iff.mpr
  intro n
  let v : ℕ → ℝ≥0 := fun i => u n (i + 1)
  have hv : ∀ i, 0 < v i := by
    intro i
    change 0 < u n (i + 1)
    have hr : (0 : ℝ) < (u n (i + 1) : ℝ) := by
      rw [huniform]
      have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have hi : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
      exact div_pos (mul_pos hT hi) hn
    exact_mod_cast hr
  have h := avram_bv_stieltjes10_original_countable_positive_grid_prejump
    X x D hD v hv
  filter_upwards [h] with ω hω
  intro i
  exact hω i
