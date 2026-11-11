-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin20_original_true_upper_exit_spatial_cofinality
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T08:46:18.908354+00:00
-- url     : https://prove2.me/submissions/c8063206-4ca6-484f-bfb2-97eb0b7b696b

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_mono_threshold
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_record_grid_clocks_eventually_ge_horizon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    Monotone (fun k : ℕ =>
      twoSidedExitUpTime X ((k : ℝ) + 1) ω) ∧
    (⨆ k : ℕ, twoSidedExitUpTime X ((k : ℝ) + 1) ω) = ⊤ := by
  constructor
  · intro i j hij
    have hijR : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    have hplus : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by linarith
    exact twoSidedExitUpTime_mono_threshold X
      ((i : ℝ) + 1) ((j : ℝ) + 1) hplus ω
  · by_contra hnot
    let U : ℝ≥0∞ :=
      ⨆ k : ℕ, twoSidedExitUpTime X ((k : ℝ) + 1) ω
    have hU : U ≠ ⊤ := hnot
    let T : ℝ≥0 := U.toNNReal + 1
    obtain ⟨N, hN⟩ :=
      firstUpcrossing_record_grid_clocks_eventually_ge_horizon
        X ω T 1 1 (by norm_num)
    have hTN : (T : ℝ≥0∞) ≤
        twoSidedExitUpTime X ((N : ℝ) + 1) ω := by
      simpa [twoSidedExitUpTime, T, mul_one, add_comm] using hN N le_rfl
    have hNU :
        twoSidedExitUpTime X ((N : ℝ) + 1) ω ≤ U := by
      exact le_iSup (fun k : ℕ => twoSidedExitUpTime X ((k : ℝ) + 1) ω) N
    have hUcoe : ((U.toNNReal : ℝ≥0) : ℝ≥0∞) = U :=
      ENNReal.coe_toNNReal hU
    have hsmall' : U.toNNReal < U.toNNReal + 1 := by
      exact lt_add_of_pos_right _ (by norm_num : (0 : ℝ≥0) < 1)
    have hsmall : U < (T : ℝ≥0∞) := by
      calc
        U = (U.toNNReal : ℝ≥0∞) := hUcoe.symm
        _ < ((U.toNNReal + 1 : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_lt_coe.mpr hsmall'
        _ = (T : ℝ≥0∞) := rfl
    exact (not_lt_of_ge (le_trans hTN hNU)) hsmall
