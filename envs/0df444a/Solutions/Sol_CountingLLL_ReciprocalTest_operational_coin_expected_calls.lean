-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.operational_coin_expected_calls
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:29:09.631032+00:00
-- url     : https://prove2.me/submissions/fc757cc5-0a09-4533-a7f4-65760f2e3bba

import Definitions.Def_CountingLLL_CoinCost
import Theorems.Thm_CountingLLL_ReciprocalTest_paired_streams
import Theorems.Thm_CountingLLL_ReciprocalTest_coin_expected_calls
import Theorems.Thm_CountingLLL_ReciprocalTest_coin_cost_geometric_all
set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

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



/-- The actual first-return local Coin makes 2/(2-B) oracle calls in expectation. -/
theorem solution (B : ℝ) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) :
    (∫⁻ ω, coinOracleCost ω ∂entropyLaw (ENNReal.ofReal B)) = ENNReal.ofReal (2/(2-B)) := by
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
  let T : (ℕ → Bool × Bool) → ℝ≥0∞ := fun x => ∑' k : ℕ,
    ({y : ℕ → Bool × Bool | ∀ i < k, y i = (false,false)}).indicator (1 : (ℕ → Bool × Bool) → ℝ≥0∞) x
  have hT : Measurable T := by
    apply Measurable.tsum
    intro k
    apply Measurable.indicator measurable_const
    have heq : {y : ℕ → Bool × Bool | ∀ i < k, y i = (false,false)} =
        ⋂ i : Fin k, {y | y i.val = (false,false)} := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro h i; exact h i.val i.isLt
      · intro h i hi; exact h ⟨i,hi⟩
    rw [heq]
    exact MeasurableSet.iInter fun i => (MeasurableSet.singleton _).preimage (measurable_pi_apply i.val)
  calc
    _ = ∫⁻ ω, T ((pair ∘ proj) ω) ∂entropyLaw p := by
      apply lintegral_congr
      intro ω
      exact coin_cost_geometric_all ω
    _ = ∫⁻ x, T x ∂((entropyLaw p).map (pair ∘ proj)) :=
      (lintegral_map hT (hpair.comp hproj)).symm
    _ = ENNReal.ofReal (2/(2-B)) := by
      rw [hmap]
      exact coin_expected_calls B hB0 hB1
