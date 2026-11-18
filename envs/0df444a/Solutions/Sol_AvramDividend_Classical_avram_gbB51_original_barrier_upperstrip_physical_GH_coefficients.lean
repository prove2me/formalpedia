-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB51_original_barrier_upperstrip_physical_GH_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:34:28.462205+00:00
-- url     : https://prove2.me/submissions/d1981804-69ab-431a-bb4a-adb8f5c13e36

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB38_barrier_reserve_above_cutoff_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB41_original_barrier_postpayment_rightLimit_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- On a positive upper-strip tube the original physical Gaussian coefficients are exterior. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T s : ℝ≥0)
    (ω : Ω) (hTube : ∀ u : ℝ≥0, u ≤ T →
      |X.X u ω| ≤ (1 / 400 : ℝ)) (hs : s < T)
    (q a : ℝ) (w : ℝ → ℝ) :
    let y : ℝ := (1 / 8 : ℝ) + X.X s ω -
      rightLimit (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) s ω
    (Real.exp (-(q * (s : ℝ))) *
      (if y ∈ Icc a (5 / 44 : ℝ) then deriv w y else 1) =
        Real.exp (-(q * (s : ℝ)))) ∧
    ((1 / 2 : ℝ) * Real.exp (-(q * (s : ℝ))) *
      (if y ∈ Icc a (5 / 44 : ℝ) then iteratedDeriv 2 w y else 0) = 0)
    := by
  have hR :=
    avram_gbB41_original_barrier_postpayment_rightLimit_eq
      X (1 / 8 : ℝ) ω s
  have hB :=
    avram_gbB38_barrier_reserve_above_cutoff_on_tube
      X s ω (fun u hu => hTube u (hu.trans (le_of_lt hs)))
  have hY : (5 / 44 : ℝ) <
      (1 / 8 : ℝ) + X.X s ω -
      rightLimit (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) s ω := by
    change (5 / 44 : ℝ) < (1 / 8 : ℝ) + X.X s ω -
      barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ) s ω at hB
    rw [hR]
    exact hB
  have hNot : (1 / 8 : ℝ) + X.X s ω -
      rightLimit (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) s ω ∉
        Icc a (5 / 44 : ℝ) := by
    intro hMem
    exact (not_le_of_gt hY) hMem.2
  dsimp
  simp only [if_neg hNot]
  constructor <;> ring
