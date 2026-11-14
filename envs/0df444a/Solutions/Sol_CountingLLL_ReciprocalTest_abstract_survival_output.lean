-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.abstract_survival_output
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:41:03.552733+00:00
-- url     : https://prove2.me/submissions/6827e978-badc-43e3-9544-d65dd04eb200

import Definitions.Def_CountingLLL_ContractedGF
import Definitions.Def_CountingLLL_ReciprocalTest
import Theorems.Thm_CountingLLL_ContractedWalk_abstract_counter_output_formula
import Theorems.Thm_CountingLLL_ReciprocalTest_random_uniform_survival
import Theorems.Thm_CountingLLL_ReciprocalTest_source_parameter_bounds
import Theorems.Thm_CountingLLL_ContractedWalk_upward_count_measurable_integrable

set_option autoImplicit false
open MeasureTheory CountingLLL.ContractedWalk CountingLLL.ReciprocalTest
open scoped ENNReal

private theorem bitLaw_probability' (p : ℝ≥0∞) (hp : p ≤ 1) : IsProbabilityMeasure (bitLaw p) := by
  constructor
  simp only [bitLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact tsub_add_cancel_of_le hp

theorem solution (B : ℝ) (hB0 : 0 < B) (hB1 : B < 1)
    (hB : Real.exp (-(3/10 : ℝ)) ≤ B) :
    let u := 2*(1-B)/(2-B)
    let θ := u^2/(1-u+u^2)
    let ν := (bitLaw (ENNReal.ofReal u)).prod (tapeLaw (ENNReal.ofReal θ))
    1 - (((ν.prod (Measure.infinitePi fun i : ℕ => uniformLaw (i+1)))
       {p : (Bool × Tape) × ((i : ℕ) → Fin (i+2)) |
          ∀ i < (if p.1.1 then 1 + upwardCount p.1.2 3 else upwardCount p.1.2 1),
            (p.2 i).val ≠ 0}).toReal)/2 = 1/(2*B) := by
  let u : ℝ := 2*(1-B)/(2-B)
  let θ : ℝ := u^2/(1-u+u^2)
  have huθ := source_parameter_bounds B hB (by linarith)
  change 0 ≤ u ∧ u < 33/80 ∧ 0 ≤ θ ∧ θ < 9/40 at huθ
  have hp : ENNReal.ofReal u ≤ 1 := by
    have hh : u ≤ (1:ℝ) := by linarith [huθ.2.1]
    simpa using ENNReal.ofReal_le_ofReal hh
  have hq : ENNReal.ofReal θ ≤ 1 := by
    have hh : θ ≤ (1:ℝ) := by linarith [huθ.2.2.2]
    simpa using ENNReal.ofReal_le_ofReal hh
  letI : IsProbabilityMeasure (bitLaw (ENNReal.ofReal u)) := bitLaw_probability' _ hp
  letI : IsProbabilityMeasure (bitLaw (ENNReal.ofReal θ)) := bitLaw_probability' _ hq
  letI : IsProbabilityMeasure (tapeLaw (ENNReal.ofReal θ)) := by unfold tapeLaw; infer_instance
  let ν := (bitLaw (ENNReal.ofReal u)).prod (tapeLaw (ENNReal.ofReal θ))
  letI : IsProbabilityMeasure ν := inferInstance
  let K : Bool × Tape → ℕ := fun x => if x.1 then 1+upwardCount x.2 3 else upwardCount x.2 1
  have hK : Measurable K := by
    apply Measurable.ite ((MeasurableSet.singleton true).preimage measurable_fst)
    · exact measurable_const.add ((upward_count_measurable_integrable.1 3).comp measurable_snd)
    · exact (upward_count_measurable_integrable.1 1).comp measurable_snd
  let f : Bool × Tape → ℝ := fun x => 1/((K x : ℝ)+1)
  have hfmeas : Measurable f := by fun_prop
  have hf0 : ∀ x, 0 ≤ f x := by intro x; positivity
  have hf1 : ∀ x, f x ≤ 1 := by intro x; dsimp [f]; apply (div_le_one₀ (by positivity)).2; have := Nat.cast_nonneg (α := ℝ) (K x); linarith
  have hfint : Integrable f ν := by
    apply (integrable_const (1:ℝ)).mono' hfmeas.aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
    exact hf1 x
  have h_lintegral : (∫⁻ x, 1/(K x+1 : ℝ≥0∞) ∂ν) = ENNReal.ofReal (∫ x, f x ∂ν) := by
    rw [ofReal_integral_eq_lintegral_ofReal hfint (Filter.Eventually.of_forall hf0)]
    apply lintegral_congr
    intro x
    change (1 : ℝ≥0∞)/(K x+1) = ENNReal.ofReal ((1:ℝ)/((K x:ℝ)+1))
    rw [ENNReal.ofReal_div_of_pos (by positivity : (0:ℝ) < (K x : ℝ)+1)]
    simp [ENNReal.ofReal_add (by positivity : (0:ℝ) ≤ (K x : ℝ))]
  have hs := random_uniform_survival ν K hK
  rw [h_lintegral] at hs
  have hformula := abstract_counter_output_formula B hB0 hB1 hB
  change 1-(∫ x, f x ∂ν)/2 = 1/(2*B) at hformula
  change 1 - (((ν.prod (Measure.infinitePi fun i : ℕ => uniformLaw (i+1)))
       {p : (Bool × Tape) × ((i : ℕ) → Fin (i+2)) | ∀ i < K p.1, (p.2 i).val ≠ 0}).toReal)/2 = _
  rw [hs, ENNReal.toReal_ofReal (integral_nonneg hf0)]
  exact hformula
