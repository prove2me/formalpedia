-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.contracted_up_probability
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:19:47.449013+00:00
-- url     : https://prove2.me/submissions/4be4125c-656a-4b27-b2d2-81f13730d763

import Theorems.Thm_CountingLLL_RandomRAM_iid_first_exit
import Definitions.Def_CountingLLL_ReciprocalTest

set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

private theorem oracleLaw_probability (B : ℝ≥0∞) (hB : B ≤ 1) : IsProbabilityMeasure (oracleLaw B) := by
  constructor
  simp only [oracleLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [add_comm, tsub_add_cancel_of_le hB]

theorem solution (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    let ν := (oracleLaw (ENNReal.ofReal (1-u))).prod (oracleLaw (ENNReal.ofReal (1-u)))
    let μ := Measure.infinitePi fun _ : ℕ => ν
    μ {ω : ℕ → Bool × Bool | ∃ n, (∀ i < n, ω i = (true,false)) ∧ ω n = (true,true)} =
      ENNReal.ofReal (u^2/(1-u+u^2)) := by
  classical
  dsimp only
  let p := ENNReal.ofReal (1-u)
  have hp0 : 0 ≤ 1-u := by linarith
  have hp1 : p ≤ 1 := by
    have h : 1-u ≤ (1:ℝ) := by linarith
    simpa [p] using ENNReal.ofReal_le_ofReal h
  letI : IsProbabilityMeasure (oracleLaw p) := oracleLaw_probability p hp1
  let ν := (oracleLaw p).prod (oracleLaw p)
  letI : IsProbabilityMeasure ν := inferInstance
  let S : Set (Bool × Bool) := {(true,false)}
  let T : Set (Bool × Bool) := {(true,true)}
  have hs : MeasurableSet S := MeasurableSet.singleton _
  have ht : MeasurableSet T := MeasurableSet.singleton _
  have hd : Disjoint S T := by simp [S,T]
  have h := CountingLLL.RandomRAM.iid_first_exit ν S T hs ht hd
  have hone : (1 : ℝ≥0∞) - p = ENNReal.ofReal u := by
    dsimp [p]
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hp0]
    congr 1
    ring
  have hsval : ν S = ENNReal.ofReal (u*(1-u)) := by
    have heq : S = ({true} : Set Bool) ×ˢ ({false} : Set Bool) := by ext ⟨a,b⟩; simp [S]
    rw [heq, Measure.prod_prod]
    simp [ν, oracleLaw, hone, p, ENNReal.ofReal_mul hu0]
  have htval : ν T = ENNReal.ofReal (u^2) := by
    have heq : T = ({true} : Set Bool) ×ˢ ({true} : Set Bool) := by ext ⟨a,b⟩; simp [T]
    rw [heq, Measure.prod_prod]
    simp [ν, oracleLaw, hone, p, ENNReal.ofReal_mul hu0, pow_two]
  have hden : 0 < (1-u+u^2 : ℝ) := by nlinarith [sq_nonneg u]
  have hdenEq : (1 : ℝ≥0∞) - ENNReal.ofReal (u*(1-u)) = ENNReal.ofReal (1-u+u^2) := by
    have hh := (ENNReal.ofReal_sub 1 (mul_nonneg hu0 hp0)).symm
    have hid : (1:ℝ) - u*(1-u) = 1-u+u^2 := by ring
    simpa [hid] using hh
  rw [hsval, htval, hdenEq, ← ENNReal.ofReal_div_of_pos hden] at h
  simpa [S,T,ν,p] using h
