-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_actual_first_mark_count_zero_before_and_one_at_arrival_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T12:46:39.856529+00:00
-- url     : https://prove2.me/submissions/6a7d61c9-5292-4e2c-be19-b542811028d2

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_rateone_size2_count_one_at_first_mark
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (τ Y : ℕ → Ω → ℝ)
    (hJ : IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      (Measure.dirac (-2 : ℝ)) μ) :
    ∀ᵐ ω ∂μ,
      (∀ t : ℝ≥0, (t : ℝ) < arrival τ 0 ω →
        jumpCount (fun n => arrival τ n ω) (t : ℝ) = 0) ∧
      jumpCount (fun n => arrival τ n ω) (arrival τ 0 ω) = 1 := by
  have hCount :
      ∀ᵐ ω ∂μ,
        jumpCount (fun n => arrival τ n ω) (arrival τ 0 ω) = 1 :=
    avram_jump6_A_original_rateone_size2_count_one_at_first_mark τ Y hJ
  filter_upwards [hCount] with ω hω
  constructor
  · intro t ht
    apply Nat.eq_zero_of_le_zero
    exact Nat.sInf_le (show (0 : ℕ) ∈
      {n : ℕ | (t : ℝ) < arrival τ n ω} from ht)
  · exact hω
