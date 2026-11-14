-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.coin_probability
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:52:59.330193+00:00
-- url     : https://prove2.me/submissions/0f14d50e-a4a0-4d4d-9e16-9c9e4b6b42d6

import Theorems.Thm_CountingLLL_RandomRAM_reciprocal_expected_cost
import Definitions.Def_CountingLLL_ReciprocalTest

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

private theorem first_exit {β : Type} [MeasurableSpace β] (ν : Measure β) [IsProbabilityMeasure ν]
    (S T : Set β) (hS : MeasurableSet S) (hT : MeasurableSet T) (hst : Disjoint S T) :
    let μ := Measure.infinitePi fun _ : ℕ => ν
    μ {ω : ℕ → β | ∃ n, (∀ i < n, ω i ∈ S) ∧ ω n ∈ T} = ν T / (1 - ν S) := by
  classical
  dsimp only
  let E : Set (ℕ → β) := {ω | ∃ n, (∀ i < n, ω i ∈ S) ∧ ω n ∈ T}
  have hE : MeasurableSet E := by
    have hEq : E = ⋃ n : ℕ, (⋂ i : Fin n, {ω : ℕ → β | ω i.val ∈ S}) ∩ {ω | ω n ∈ T} := by
      ext ω
      simp only [E, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter]
      constructor
      · rintro ⟨n, hn, h⟩
        exact ⟨n, fun i => hn i.val i.isLt, h⟩
      · rintro ⟨n, hn, h⟩
        exact ⟨n, fun i hi => hn ⟨i, hi⟩, h⟩
    rw [hEq]
    exact MeasurableSet.iUnion fun n => (MeasurableSet.iInter fun i => hS.preimage (measurable_pi_apply i.val)).inter (hT.preimage (measurable_pi_apply n))
  have hpoint (ω : ℕ → β) : (∑' n : ℕ,
      ({ω' : ℕ → β | ∀ i < n, ω' i ∈ S}).indicator (fun ω => T.indicator (1 : β → ℝ≥0∞) (ω n)) ω) = E.indicator 1 ω := by
    by_cases he : ω ∈ E
    · obtain ⟨n, hn, ht⟩ := he
      have he' : ω ∈ E := ⟨n, hn, ht⟩
      rw [tsum_eq_single n]
      · have hw : ω ∈ {ω' : ℕ → β | ∀ i < n, ω' i ∈ S} := hn
        rw [Set.indicator_of_mem hw, Set.indicator_of_mem ht, Set.indicator_of_mem he']
        rfl
      · intro m hmn
        by_cases hm : ∀ i < m, ω i ∈ S
        · by_cases hmt : ω m ∈ T
          · have : m < n ∨ n < m := lt_or_gt_of_ne hmn
            rcases this with hmn' | hnm
            · exact False.elim ((Set.disjoint_left.mp hst (hn m hmn')) hmt)
            · exact False.elim ((Set.disjoint_left.mp hst (hm n hnm)) ht)
          · simp [hm, hmt]
        · simp [hm]
    · have hzero (n : ℕ) : ({ω' : ℕ → β | ∀ i < n, ω' i ∈ S}).indicator (fun ω => T.indicator (1 : β → ℝ≥0∞) (ω n)) ω = 0 := by
        by_cases hn : ∀ i < n, ω i ∈ S
        · have ht : ω n ∉ T := by intro ht; exact he ⟨n, hn, ht⟩
          simp [hn, ht]
        · simp [hn]
      simp [hzero, he]
  have hc := CountingLLL.RandomRAM.reciprocal_expected_cost ν S hS (T.indicator (1 : β → ℝ≥0∞)) (measurable_one.indicator hT)
  have hi : (∫⁻ ω, ∑' n : ℕ,
      ({ω' : ℕ → β | ∀ i < n, ω' i ∈ S}).indicator (fun ω => T.indicator (1 : β → ℝ≥0∞) (ω n)) ω ∂(Measure.infinitePi fun _ : ℕ => ν)) = (Measure.infinitePi fun _ : ℕ => ν) E := by
    rw [lintegral_congr hpoint, lintegral_indicator_one hE]
  rw [hi, lintegral_indicator_one hT] at hc
  exact hc

open CountingLLL.ReciprocalTest

private theorem uniformLaw_probability (n : ℕ) : IsProbabilityMeasure (uniformLaw n) := by
  constructor
  simp [uniformLaw, Measure.smul_apply, Measure.count_apply]
  apply ENNReal.inv_mul_cancel <;> simp


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
    μ {ω : ℕ → Bool × Bool | ∃ n, (∀ i < n, ω i = (false, false)) ∧ (ω n).1 = true} =
      ENNReal.ofReal (2 * (1 - B) / (2 - B)) := by
  classical
  dsimp only
  let p := ENNReal.ofReal B
  have hp : p ≤ 1 := by simpa [p] using ENNReal.ofReal_le_ofReal hB1
  letI : IsProbabilityMeasure (oracleLaw p) := oracleLaw_probability p hp
  letI : IsProbabilityMeasure fairLaw := fairLaw_probability
  let ν := (oracleLaw p).prod fairLaw
  letI : IsProbabilityMeasure ν := inferInstance
  let S : Set (Bool × Bool) := {(false, false)}
  let T : Set (Bool × Bool) := {x | x.1 = true}
  have hs : MeasurableSet S := MeasurableSet.singleton _
  have ht : MeasurableSet T := by
    change MeasurableSet (Prod.fst ⁻¹' ({true} : Set Bool))
    exact measurable_fst (MeasurableSet.singleton _)
  have hdis : Disjoint S T := by simp [S, T, Set.disjoint_left]
  have h := first_exit ν S T hs ht hdis
  have hsval : ν S = ENNReal.ofReal (B/2) := by
    have heq : S = ({false} : Set Bool) ×ˢ ({false} : Set Bool) := by ext ⟨a,b⟩; simp [S]
    rw [heq, Measure.prod_prod]
    simp [ν, oracleLaw, fairLaw, p, ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
    simp [div_eq_mul_inv]
  have htval : ν T = ENNReal.ofReal (1-B) := by
    have heq : T = ({true} : Set Bool) ×ˢ (Set.univ : Set Bool) := by ext ⟨a,b⟩; simp [T]
    rw [heq, Measure.prod_prod]
    rw [fairLaw_probability.measure_univ]
    simp [ν, oracleLaw, p, ENNReal.ofReal_sub _ hB0]
  rw [hsval, htval] at h
  have hden : 0 < (1-B/2 : ℝ) := by linarith
  have hdenEq : (1 : ℝ≥0∞) - ENNReal.ofReal (B/2) = ENNReal.ofReal (1-B/2) := by
    simpa using (ENNReal.ofReal_sub 1 (by positivity : (0:ℝ) ≤ B/2)).symm
  rw [hdenEq, ← ENNReal.ofReal_div_of_pos hden] at h
  have hid : (1-B)/(1-B/2) = 2*(1-B)/(2-B) := by field_simp
  rw [hid] at h
  simpa [S, T, ν, p] using h
