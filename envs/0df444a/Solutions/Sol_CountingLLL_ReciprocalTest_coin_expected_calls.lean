-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.coin_expected_calls
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:54:25.996498+00:00
-- url     : https://prove2.me/submissions/00a25911-fad1-47be-bb12-6b9bae7f569b

import Theorems.Thm_CountingLLL_RandomRAM_reciprocal_expected_cost
import Definitions.Def_CountingLLL_ReciprocalTest

open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal BigOperators

private theorem oracleLaw_probability (B : ℝ≥0∞) (hB : B ≤ 1) : IsProbabilityMeasure (oracleLaw B) := by
  constructor
  simp only [oracleLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [add_comm, tsub_add_cancel_of_le hB]

private theorem fairLaw_probability : IsProbabilityMeasure fairLaw := by
  constructor
  simp only [fairLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← two_mul]
  rw [one_div]
  exact ENNReal.mul_inv_cancel (by norm_num) (by simp)



theorem solution (B : ℝ) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) :
    let ν := (oracleLaw (ENNReal.ofReal B)).prod fairLaw
    let μ := Measure.infinitePi fun _ : ℕ => ν
    (∫⁻ ω, ∑' n : ℕ, ({ω' : ℕ → Bool × Bool | ∀ i < n, ω' i = (false, false)}).indicator (1 : (ℕ → Bool × Bool) → ℝ≥0∞) ω ∂μ) =
      ENNReal.ofReal (2 / (2 - B)) := by
  classical
  dsimp only
  let p := ENNReal.ofReal B
  have hp : p ≤ 1 := by simpa [p] using ENNReal.ofReal_le_ofReal hB1
  letI : IsProbabilityMeasure (oracleLaw p) := oracleLaw_probability p hp
  letI : IsProbabilityMeasure fairLaw := fairLaw_probability
  let ν := (oracleLaw p).prod fairLaw
  letI : IsProbabilityMeasure ν := inferInstance
  let S : Set (Bool × Bool) := {(false, false)}
  have hs : MeasurableSet S := MeasurableSet.singleton _
  have hsval : ν S = ENNReal.ofReal (B/2) := by
    have heq : S = ({false} : Set Bool) ×ˢ ({false} : Set Bool) := by ext ⟨a,b⟩; simp [S]
    rw [heq, Measure.prod_prod]
    simp [ν, oracleLaw, fairLaw, p, ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
    simp [div_eq_mul_inv]
  have h := CountingLLL.RandomRAM.reciprocal_expected_cost ν S hs (1 : Bool × Bool → ℝ≥0∞) measurable_one
  have hden : 0 < (1-B/2 : ℝ) := by linarith
  have hdenEq : (1 : ℝ≥0∞) - ENNReal.ofReal (B/2) = ENNReal.ofReal (1-B/2) := by
    simpa using (ENNReal.ofReal_sub 1 (by positivity : (0:ℝ) ≤ B/2)).symm
  rw [hsval, hdenEq] at h
  have h1 : (∫⁻ _x : Bool × Bool, (1 : Bool × Bool → ℝ≥0∞) _x ∂ν) = 1 := by simp
  rw [h1] at h
  have hreal : (1 : ℝ≥0∞) / ENNReal.ofReal (1-B/2) = ENNReal.ofReal (1/(1-B/2)) := by
    simpa using (ENNReal.ofReal_div_of_pos (x := (1:ℝ)) hden).symm
  rw [hreal] at h
  have hid : (1:ℝ)/(1-B/2) = 2/(2-B) := by field_simp
  rw [hid] at h
  simp only [Pi.one_apply] at h
  have hf : (fun _ : ℕ → Bool × Bool => (1 : ℝ≥0∞)) = 1 := by funext; rfl
  rw [hf] at h
  simpa [S, ν, p] using h
