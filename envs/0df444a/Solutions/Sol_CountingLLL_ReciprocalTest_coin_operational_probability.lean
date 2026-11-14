-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.coin_operational_probability
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:03:33.858955+00:00
-- url     : https://prove2.me/submissions/da4688b1-f9f5-42dc-a410-c08597295eae

import Definitions.Def_CountingLLL_ReciprocalTest
import Theorems.Thm_CountingLLL_ReciprocalTest_paired_streams
import Theorems.Thm_CountingLLL_ReciprocalTest_coin_success_iff
import Theorems.Thm_CountingLLL_ReciprocalTest_coin_probability

set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

noncomputable section

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
    entropyLaw (ENNReal.ofReal B)
      {ω | ∃ t, ((step ω)^[t] ({phase := .coinOracle .initial} : State)).phase = .initialCheck} =
      ENNReal.ofReal (2*(1-B)/(2-B)) := by
  classical
  let p := ENNReal.ofReal B
  have hp : p ≤ 1 := by simpa [p] using ENNReal.ofReal_le_ofReal hB1
  letI : IsProbabilityMeasure (oracleLaw p) := oracleLaw_probability p hp
  letI : IsProbabilityMeasure fairLaw := fairLaw_probability
  letI (a : ℕ × ℕ) : IsProbabilityMeasure (uniformLaw a.1) := uniformLaw_probability a.1
  let μo := Measure.infinitePi fun _ : ℕ => oracleLaw p
  let μf := Measure.infinitePi fun _ : ℕ => fairLaw
  let μu := Measure.infinitePi fun a : ℕ × ℕ => uniformLaw a.1
  let proj : Entropy → (ℕ → Bool) × (ℕ → Bool) := fun ω => (ω.1, ω.2.1)
  have hproj : Measurable proj := by fun_prop
  have hm : (entropyLaw p).map proj = μo.prod μf := by
    change (μo.prod (μf.prod μu)).map (Prod.map id Prod.fst) = _
    rw [← Measure.map_prod_map μo (μf.prod μu) measurable_id measurable_fst]
    simp
  let pair : ((ℕ → Bool) × (ℕ → Bool)) → (ℕ → Bool × Bool) := fun x n => (x.1 n, x.2 n)
  have hpair : Measurable pair := by fun_prop
  have hmap : (entropyLaw p).map (pair ∘ proj) = Measure.infinitePi (fun _ : ℕ => (oracleLaw p).prod fairLaw) := by
    rw [← Measure.map_map hpair hproj, hm]
    exact paired_streams (oracleLaw p) fairLaw
  let E : Set (ℕ → Bool × Bool) := {x | ∃ n, (∀ i < n, x i = (false,false)) ∧ (x n).1 = true}
  have hE : MeasurableSet E := by
    have he : E = ⋃ n : ℕ, (⋂ i : Fin n, {x : ℕ → Bool × Bool | x i.val = (false,false)}) ∩ {x | (x n).1 = true} := by
      ext x
      simp only [E, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter]
      constructor
      · rintro ⟨n, hn, h⟩; exact ⟨n, fun i => hn i.val i.isLt, h⟩
      · rintro ⟨n, hn, h⟩; exact ⟨n, fun i hi => hn ⟨i, hi⟩, h⟩
    rw [he]
    apply MeasurableSet.iUnion
    intro n
    apply MeasurableSet.inter
    · exact MeasurableSet.iInter fun i => (MeasurableSet.singleton _).preimage (measurable_pi_apply i.val)
    · exact (MeasurableSet.singleton true).preimage (measurable_fst.comp (measurable_pi_apply n))
  have heq : {ω : Entropy | ∃ t, ((step ω)^[t] ({phase := .coinOracle .initial} : State)).phase = .initialCheck} = (pair ∘ proj) ⁻¹' E := by
    ext ω
    have hi := coin_success_iff ω
    simpa [E, pair, proj, Prod.ext_iff] using hi
  rw [heq, ← Measure.map_apply (hpair.comp hproj) hE, hmap]
  exact coin_probability B hB0 hB1
