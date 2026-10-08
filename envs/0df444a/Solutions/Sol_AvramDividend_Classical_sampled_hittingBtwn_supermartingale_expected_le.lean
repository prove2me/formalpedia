-- Prove2me | solution 1 for AvramDividend.Classical.sampled_hittingBtwn_supermartingale_expected_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:33:42.265441+00:00
-- url     : https://prove2.me/submissions/7c85729f-4209-421e-acd6-231cd75dc755

import Mathlib
import Theorems.Thm_AvramDividend_Classical_supermartingale_expected_stoppedValue_antitone_nat

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {𝓖 : Filtration ℕ mΩ} [SigmaFiniteFiltration μ 𝓖]
    (U V : ℕ → Ω → ℝ)
    (hU : Adapted 𝓖 U)
    (hV : Supermartingale V 𝓖 μ)
    (N : ℕ) :
    (∫ ω, stoppedValue V
      (fun ω => ((hittingBtwn U (Iio (0 : ℝ)) 0 N ω : ℕ) : WithTop ℕ)) ω ∂μ) ≤
      ∫ ω, V 0 ω ∂μ := by
  let τ : Ω → WithTop ℕ := fun _ => 0
  let π : Ω → WithTop ℕ :=
    fun ω => ((hittingBtwn U (Iio (0 : ℝ)) 0 N ω : ℕ) : WithTop ℕ)
  have hτ : IsStoppingTime 𝓖 τ := by
    exact isStoppingTime_const 𝓖 0
  have hπ : IsStoppingTime 𝓖 π := by
    exact hU.isStoppingTime_hittingBtwn measurableSet_Iio
  have hle : τ ≤ π := by
    intro ω
    change ((0 : ℕ) : WithTop ℕ) ≤
      ((hittingBtwn U (Iio (0 : ℝ)) 0 N ω : ℕ) : WithTop ℕ)
    exact WithTop.coe_le_coe.mpr
      (Nat.zero_le (hittingBtwn U (Iio (0 : ℝ)) 0 N ω))
  have hbdd : ∀ ω, π ω ≤ (N : WithTop ℕ) := by
    intro ω
    change ((hittingBtwn U (Iio (0 : ℝ)) 0 N ω : ℕ) : WithTop ℕ) ≤
      ((N : ℕ) : WithTop ℕ)
    exact WithTop.coe_le_coe.mpr
      (hittingBtwn_mem_Icc
        (u := U) (s := Iio (0 : ℝ)) (Nat.zero_le N) ω).2
  have hh :=
    AvramDividend.Classical.supermartingale_expected_stoppedValue_antitone_nat
      hV hτ hπ hle hbdd
  calc
    (∫ ω, stoppedValue V
      (fun ω => ((hittingBtwn U (Iio (0 : ℝ)) 0 N ω : ℕ) : WithTop ℕ)) ω ∂μ) ≤
        ∫ ω, stoppedValue V τ ω ∂μ := by
          exact hh
    _ = ∫ ω, V 0 ω ∂μ := by
          simp [τ, stoppedValue]
