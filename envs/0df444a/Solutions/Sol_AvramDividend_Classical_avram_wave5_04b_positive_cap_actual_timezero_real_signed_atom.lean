-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_positive_cap_actual_timezero_real_signed_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:13:53.91213+00:00
-- url     : https://prove2.me/submissions/90de7fe5-57f2-4817-adbd-1ebeb635ab9f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_cap_original_discounted_cell_signed_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_cap_original_global_closed_stieltjes_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_closed_horizon_real_stieltjes_partition_finite
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Real signed control of the actual time-zero dividend atom uniformly at all positive caps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) :
    (∫⁻ s in ({0} : Set ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      (V (x + X.X 0 ω - rightLimit D 0 ω) - V (x + X.X 0 ω)) ≤ 0 := by
  have hAdmissible : IsAdmissible X x D := hD.1
  have hStrategy : IsDividendStrategy 𝓕 D := hAdmissible.1
  have hZeroJump := hAdmissible.2 ω (0 : ℝ≥0) (Or.inl rfl)
  have hCover0 : rightLimit D 0 ω ≤ x + X.X 0 ω := by
    dsimp [riskProcess] at hZeroJump
    linarith only [hZeroJump]
  have hD0nonneg : 0 ≤ D 0 ω := by
    have hm := hStrategy.2.1 ω
      (show (0 : ℝ≥0) ≤ (0 : ℝ≥0) from zero_le)
    simpa only [hStrategy.1 ω] using hm
  have hRight0nonneg : 0 ≤ rightLimit D 0 ω := le_trans hD0nonneg
    (dividendStrategy_le_rightLimit D hStrategy ω 0)
  have hOrder0 : x + X.X 0 ω - rightLimit D 0 ω ≤ x + X.X 0 ω := by
    linarith only [hRight0nonneg]
  have hSec0 := avram_wave5_04b_positive_ennreal_cap_extension_global_secant
    C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
    (x + X.X 0 ω - rightLimit D 0 ω) (x + X.X 0 ω)
    (sub_nonneg.mpr hCover0) hOrder0
  have hDrop0 : 0 ≤
      V (x + X.X 0 ω) - V (x + X.X 0 ω - rightLimit D 0 ω) := by
    linarith only [hSec0, hRight0nonneg]
  have hAtom := avram_wave5_04b_positive_cap_original_global_closed_stieltjes_budget
    X x C hC q hq w V hw_cont hw_smooth hw_grad hVtop hVfinite
    D hD ω 0 (Or.inl rfl)
  have hAtomReal := ENNReal.toReal_mono (by simp) hAtom
  rw [ENNReal.toReal_ofReal hDrop0] at hAtomReal
  have hSet0 : Icc (0 : ℝ) ((0 : ℝ≥0) : ℝ) = ({0} : Set ℝ) := by
    simpa using (Icc_self (0 : ℝ))
  rw [hSet0] at hAtomReal
  linarith only [hAtomReal]
