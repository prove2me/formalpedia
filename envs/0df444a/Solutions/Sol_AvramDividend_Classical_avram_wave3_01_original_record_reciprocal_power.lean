-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_original_record_reciprocal_power
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T17:55:25.45999+00:00
-- url     : https://prove2.me/submissions/7f779dbb-5974-4e45-b4c3-6248444cfa22

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_uncapped_reflected_record_discount_semigroup

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The genuine reflected-killed first-record discount on a reciprocal
grid is an exact root of its unit-height discount. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a q : ℝ) (ha : 0 < a) (hq : 0 < q) :
    ∀ n : ℕ,
      (∫⁻ ω, if twoSidedExitUpTime X (1 / ((n : ℝ) + 1)) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X
            (1 / ((n : ℝ) + 1)) ω).toReal)))
      else 0 ∂P) ^ (n + 1) =
      (∫⁻ ω, if twoSidedExitUpTime X 1 ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
      else 0 ∂P) := by
  let F : ℝ → ℝ≥0∞ := fun h =>
    ∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
      ENNReal.ofReal
        (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
    else 0 ∂P
  have hsem (b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
      F (b + c) = F b * F c := by
    simpa only [F] using
      (avram_wave3_01_uncapped_reflected_record_discount_semigroup
        X a b c q ha hb hc hq)
  have hpow (y : ℝ) (hy : 0 < y) :
      ∀ n : ℕ, F (((n : ℝ) + 1) * y) = (F y) ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
        norm_num
    | succ n ih =>
        have hn0 : 0 < ((n : ℝ) + 1) * y :=
          mul_pos (by positivity) hy
        have hadd : (((n + 1 : ℕ) : ℝ) + 1) * y =
            ((n : ℝ) + 1) * y + y := by
          push_cast
          ring
        rw [hadd, hsem _ _ hn0 hy, ih]
        simp only [pow_succ]
  intro n
  change (F (1 / ((n : ℝ) + 1))) ^ (n + 1) = F 1
  have hunit : ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) = 1 := by
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hn]
  have hresult := hpow (1 / ((n : ℝ) + 1)) (by positivity) n
  rw [hunit] at hresult
  exact hresult.symm
