-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB306_original_real_time_good_cell_gaussian_fibre_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:01:00.240513+00:00
-- url     : https://prove2.me/submissions/e96f650e-15a9-4806-b699-bf236d76bc48

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB266_original_zerojump_good_cell_fixed_level_gaussian_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original Gaussian anti-concentration on a physical real-time mesh cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (m i : ℕ) (hm : 0 < m) (t : ℝ)
    (ht : t ∈ Set.Ioo
      ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))
      (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4))))
    (x b : ℝ) :
    P {ω | D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) ω -
        D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) ω ≤
          1 / ((m : ℝ) ^ 3) ∧
      x + X.X (Real.toNNReal t) ω - rightLimit D (Real.toNNReal t) ω = b} ≤
    ENNReal.ofReal
      ((Real.sqrt (2 * Real.pi *
        (((NNReal.mk (X.σ ^ 2) (sq_nonneg X.σ)) *
          ((Real.toNNReal t -
            ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) : ℝ≥0) : NNReal) : ℝ))))⁻¹) *
      ENNReal.ofReal (1 / ((m : ℝ) ^ 3)) := by
  let s : ℝ≥0 := (i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))
  let u : ℝ≥0 := ((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))
  have hsR : (s : ℝ) = (i : ℝ) * (1 / ((m : ℝ) ^ 4)) := by
    dsimp [s]
    norm_cast
  have huR : (u : ℝ) = ((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4)) := by
    dsimp [u]
    push_cast
    norm_cast
  have htNonneg : 0 ≤ t := by
    exact le_trans (by positivity) (le_of_lt ht.1)
  have htCast : ((Real.toNNReal t : ℝ≥0) : ℝ) = t :=
    Real.coe_toNNReal _ htNonneg
  have hstR : (s : ℝ) < (Real.toNNReal t : ℝ) := by
    rw [hsR, htCast]
    exact ht.1
  have htuR : (Real.toNNReal t : ℝ) < (u : ℝ) := by
    rw [huR, htCast]
    exact ht.2
  have hst : s < Real.toNNReal t := by exact_mod_cast hstR
  have htu : Real.toNNReal t < u := by exact_mod_cast htuR
  exact avram_gbB266_original_zerojump_good_cell_fixed_level_gaussian_bound
    X hBV hν D hD s (Real.toNNReal t) u hst htu
    x b (1 / ((m : ℝ) ^ 3)) (by positivity)
