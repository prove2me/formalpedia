-- Prove2me | solution 1 for CountingLLL.ContractedWalk.initial_counter_generating_function
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:16:27.946742+00:00
-- url     : https://prove2.me/submissions/b7f2370e-b16c-49d1-a93e-9a815f805ad8

import Definitions.Def_CountingLLL_ContractedGF
import Theorems.Thm_CountingLLL_ContractedWalk_generating_function_factor
import Theorems.Thm_CountingLLL_ContractedWalk_upward_count_measurable_integrable

set_option autoImplicit false
open MeasureTheory CountingLLL.ContractedWalk
open scoped ENNReal

private theorem bitLaw_probability' (p : ℝ≥0∞) (hp : p ≤ 1) : IsProbabilityMeasure (bitLaw p) := by
  constructor
  simp only [bitLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact tsub_add_cancel_of_le hp

theorem solution (u θ z : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hθ0 : 0 ≤ θ) (hθ : θ < 1/3) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    (∫ x : Bool × Tape, z ^ (if x.1 then 1 + upwardCount x.2 3 else upwardCount x.2 1)
      ∂((bitLaw (ENNReal.ofReal u)).prod (tapeLaw (ENNReal.ofReal θ)))) =
      (1-u)*generatingFunction θ z + u*z*(generatingFunction θ z)^3 := by
  classical
  let p := ENNReal.ofReal u
  let q := ENNReal.ofReal θ
  have hp : p ≤ 1 := by simpa [p] using ENNReal.ofReal_le_ofReal hu1
  have hq : q ≤ 1 := by
    have hreal : θ ≤ (1:ℝ) := by linarith
    simpa [q] using ENNReal.ofReal_le_ofReal hreal
  letI : IsProbabilityMeasure (bitLaw p) := bitLaw_probability' p hp
  letI : IsProbabilityMeasure (bitLaw q) := bitLaw_probability' q hq
  letI : IsProbabilityMeasure (tapeLaw q) := by unfold tapeLaw; infer_instance
  letI : IsProbabilityMeasure ((bitLaw p).prod (tapeLaw q)) := inferInstance
  let cnt : Bool × Tape → ℕ := fun x => if x.1 then 1 + upwardCount x.2 3 else upwardCount x.2 1
  have hcnt : Measurable cnt := by
    apply Measurable.ite ((MeasurableSet.singleton true).preimage measurable_fst)
    · exact measurable_const.add ((upward_count_measurable_integrable.1 3).comp measurable_snd)
    · exact (upward_count_measurable_integrable.1 1).comp measurable_snd
  have hm : Measurable (fun x : Bool × Tape => z ^ cnt x) := hcnt.const_pow z
  have hInt : Integrable (fun x : Bool × Tape => z ^ cnt x) ((bitLaw p).prod (tapeLaw q)) := by
    apply (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hz0 _)]
    exact pow_le_one₀ hz0 hz1
  change (∫ x : Bool × Tape, z ^ cnt x ∂((bitLaw p).prod (tapeLaw q))) = _
  rw [integral_prod _ hInt]
  let F : Bool → ℝ := fun b => ∫ ω : Tape, z ^ cnt (b,ω) ∂tapeLaw q
  change (∫ b, F b ∂bitLaw p) = _
  have hi0 : Integrable F ((1-p) • Measure.dirac false) := (integrable_dirac (by simp)).smul_measure (ne_of_lt (lt_of_le_of_lt tsub_le_self (by simp)))
  have hi1 : Integrable F (p • Measure.dirac true) := (integrable_dirac (by simp)).smul_measure (ne_of_lt (lt_of_le_of_lt hp (by simp)))
  rw [show bitLaw p = (1-p) • Measure.dirac false + p • Measure.dirac true from rfl, integral_add_measure hi0 hi1]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul, ENNReal.toReal_sub_of_le hp (by simp), ENNReal.toReal_one, p, ENNReal.toReal_ofReal hu0]
  have hFfalse : F false = generatingFunction θ z := by rfl
  have hFtrue : F true = z * (∫ ω : Tape, z ^ upwardCount ω 3 ∂tapeLaw q) := by
    dsimp [F,cnt]
    simp only [pow_add, pow_one]
    rw [integral_const_mul]
  have hF2 := generating_function_factor θ z hθ0 hθ hz0 hz1 1
  have hF3 := generating_function_factor θ z hθ0 hθ hz0 hz1 2
  norm_num only at hF2 hF3
  rw [hFfalse,hFtrue,hF3,hF2]
  dsimp [generatingFunction]
  ring
