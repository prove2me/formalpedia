-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_reflected_record_factor_continuous_depth_no_grids
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T17:44:15.8712+00:00
-- url     : https://prove2.me/submissions/57c30bf7-d0a0-4d0a-8e67-b902058d84fd

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat05_cantor_rational_schedule_dense
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_reflected_record_factor_continuous_depth

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

/-- Deterministic dense and shrinking grids eliminate auxiliary schedule
hypotheses from the genuine reflected-record depth-continuity theorem. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b q : ℝ) (hb : 0 ≤ b) (hq : 0 < q)
    (hjump : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤) :
    ContinuousOn (fun a : ℝ =>
      ∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
      else 0 ∂P) (Ioi 0) := by
  let times : ℕ → ℝ≥0 := fun j =>
    ((Nat.unpair j).2 : ℝ≥0) *
      (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
  let horizons : ℕ → ℝ≥0 :=
    fun n => (1 : ℝ≥0) / ((n : ℝ≥0) + 1)
  have hdense : ∀ a c : ℝ≥0, a < c →
      ∃ m : ℕ, a < times m ∧ times m < c := by
    intro a c hac
    obtain ⟨t, ⟨n, rfl⟩, hat, htc⟩ :=
      (chat05_cantor_rational_schedule_dense :
        Dense (Set.range times)).exists_between hac
    exact ⟨n, hat, htc⟩
  have hpos : ∀ n : ℕ, 0 < horizons n := by
    intro n
    dsimp [horizons]
    positivity
  have hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε := by
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    exact ⟨n, by simpa only [horizons] using le_of_lt hn⟩
  exact avram_wave3_01_reflected_record_factor_continuous_depth
    X b q hb hq times horizons hdense hpos hcofinal hjump
