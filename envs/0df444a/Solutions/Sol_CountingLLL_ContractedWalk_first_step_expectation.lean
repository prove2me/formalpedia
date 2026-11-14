-- Prove2me | solution 1 for CountingLLL.ContractedWalk.first_step_expectation
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:46:41.96323+00:00
-- url     : https://prove2.me/submissions/5986a132-b16c-4131-b992-193acc3ab129

import Definitions.Def_CountingLLL_ContractedGF
import Theorems.Thm_CountingLLL_ContractedWalk_head_tail_independent
import Theorems.Thm_CountingLLL_ContractedWalk_iid_tail_law
import Theorems.Thm_CountingLLL_ContractedWalk_upward_count_first_step
import Theorems.Thm_CountingLLL_ContractedWalk_upward_count_measurable_integrable
import Theorems.Thm_CountingLLL_ContractedWalk_absorption_and_expected_changes

set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ContractedWalk
open scoped ENNReal BigOperators

private theorem bitLaw_probability' (p : ℝ≥0∞) (hp : p ≤ 1) : IsProbabilityMeasure (bitLaw p) := by
  constructor
  simp only [bitLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact tsub_add_cancel_of_le hp

private theorem level_ext' (ω ω' : Tape) (i t : ℕ) (h : ∀ k < t, ω k = ω' k) : level ω i t = level ω' i t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hprev : ∀ k < t, ω k = ω' k := by intro k hk; exact h k (by omega)
    have hnow := h t (by omega)
    simp only [level, ih hprev, hnow]

private theorem stop_meas' (i : ℕ) : MeasurableSet {ω : Tape | ∃ t, level ω i t = 0} := by
  classical
  have heq : {ω : Tape | ∃ t, level ω i t = 0} = ⋃ t : ℕ, {ω : Tape | level ω i t = 0} := by ext ω; simp
  rw [heq]
  apply MeasurableSet.iUnion
  intro t
  let pref : Tape → (Fin t → Bool) := fun ω j => ω j
  have hm : Measurable pref := measurable_pi_lambda _ (fun j => measurable_pi_apply j.val)
  let F : Set (Fin t → Bool) := {x | ∃ ω : Tape, pref ω = x ∧ level ω i t = 0}
  have hF : MeasurableSet F := MeasurableSet.of_discrete
  have heq' : pref ⁻¹' F = {ω : Tape | level ω i t = 0} := by
    ext ω
    constructor
    · rintro ⟨ω',hEq,hHit⟩
      have hpre : ∀ k < t, ω k = ω' k := by intro k hk; exact (congrFun hEq ⟨k,hk⟩).symm
      simpa [level_ext' ω ω' i t hpre] using hHit
    · intro hHit; exact ⟨ω,rfl,hHit⟩
  rw [←heq']
  exact hF.preimage hm

private theorem ae_stop (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ < 1/3) (i : ℕ) :
    ∀ᵐ ω ∂tapeLaw (ENNReal.ofReal θ), ∃ t, level ω i t = 0 := by
  have hp : ENNReal.ofReal θ ≤ 1 := by
    have hreal : θ ≤ (1:ℝ) := by linarith
    simpa using ENNReal.ofReal_le_ofReal hreal
  letI : IsProbabilityMeasure (bitLaw (ENNReal.ofReal θ)) := bitLaw_probability' _ hp
  letI : IsProbabilityMeasure (tapeLaw (ENNReal.ofReal θ)) := by unfold tapeLaw; infer_instance
  apply ae_iff.mpr
  have h := measure_compl (μ := tapeLaw (ENNReal.ofReal θ)) (stop_meas' i) (by simp)
  rw [measure_univ, (absorption_and_expected_changes θ h0 h1 i).1] at h
  change tapeLaw (ENNReal.ofReal θ) ({ω : Tape | ∃ t, level ω i t = 0}ᶜ) = 0
  simpa using h

theorem solution (θ z : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 1/3)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (i : ℕ) (hi : 0 < i) :
    (∫ ω : Tape, z ^ upwardCount ω i ∂tapeLaw (ENNReal.ofReal θ)) =
      (1-θ)*(∫ ω : Tape, z ^ upwardCount ω (i-1) ∂tapeLaw (ENNReal.ofReal θ)) +
      θ*z*(∫ ω : Tape, z ^ upwardCount ω (i+2) ∂tapeLaw (ENNReal.ofReal θ)) := by
  classical
  let p := ENNReal.ofReal θ
  have hp : p ≤ 1 := by
    have hreal : θ ≤ (1:ℝ) := by linarith
    simpa [p] using ENNReal.ofReal_le_ofReal hreal
  letI : IsProbabilityMeasure (bitLaw p) := bitLaw_probability' p hp
  let μ := tapeLaw p
  letI : IsProbabilityMeasure μ := by dsimp [μ,tapeLaw]; infer_instance
  let shift : Tape → Tape := fun ω n => ω (n+1)
  have hshift : Measurable shift := measurable_pi_lambda _ (fun n => measurable_pi_apply (n+1))
  have hmap : μ.map shift = μ := iid_tail_law p hp
  have htail (j : ℕ) : ∀ᵐ ω ∂μ, ∃ t, level (shift ω) j t = 0 := by
    have hae := ae_stop θ hθ0 hθ j
    change ∀ᵐ ω ∂μ, ∃ t, level ω j t = 0 at hae
    rw [← hmap] at hae
    exact (ae_map_iff hshift.aemeasurable (stop_meas' j)).1 hae
  let H0 : Bool → ℝ := fun b => if b then 0 else 1
  let H1 : Bool → ℝ := fun b => if b then 1 else 0
  let Z0 : Tape → ℝ := fun ω => z ^ upwardCount ω (i-1)
  let Z1 : Tape → ℝ := fun ω => z ^ upwardCount ω (i+2)
  have hH0 : Measurable H0 := measurable_of_countable H0
  have hH1 : Measurable H1 := measurable_of_countable H1
  have hZ0 : Measurable Z0 := (upward_count_measurable_integrable.1 (i-1)).const_pow z
  have hZ1 : Measurable Z1 := (upward_count_measurable_integrable.1 (i+2)).const_pow z
  have hZ0int : Integrable Z0 μ := upward_count_measurable_integrable.2 θ z (by linarith) hz0 hz1 (i-1)
  have hZ1int : Integrable Z1 μ := upward_count_measurable_integrable.2 θ z (by linarith) hz0 hz1 (i+2)
  have hZ0tail : Integrable (Z0 ∘ shift) μ := by
    have hh := hZ0int
    rw [← hmap] at hh
    exact hh.comp_measurable hshift
  have hZ1tail : Integrable (Z1 ∘ shift) μ := by
    have hh := hZ1int
    rw [← hmap] at hh
    exact hh.comp_measurable hshift
  have hInd := head_tail_independent p hp
  have hInd0 := hInd.comp hH0 hZ0
  have hInd1 := hInd.comp hH1 hZ1
  have hH0exp : (∫ ω : Tape, H0 (ω 0) ∂μ) = 1-θ := by
    have hm : μ.map (fun ω : Tape => ω 0) = bitLaw p := Measure.infinitePi_map_eval _ _
    rw [← integral_map (measurable_pi_apply 0).aemeasurable hH0.aestronglyMeasurable, hm]
    have hi0 : Integrable H0 ((1-p) • Measure.dirac false) := (integrable_dirac (by simp)).smul_measure (ne_of_lt (lt_of_le_of_lt tsub_le_self (by simp)))
    have hi1 : Integrable H0 (p • Measure.dirac true) := (integrable_dirac (by simp)).smul_measure (ne_of_lt (lt_of_le_of_lt hp (by simp)))
    rw [show bitLaw p = (1-p) • Measure.dirac false + p • Measure.dirac true from rfl, integral_add_measure hi0 hi1]
    simp [integral_smul_measure, integral_dirac, H0, ENNReal.toReal_sub_of_le hp (by simp), p, hθ0]
  have hH1exp : (∫ ω : Tape, H1 (ω 0) ∂μ) = θ := by
    have hm : μ.map (fun ω : Tape => ω 0) = bitLaw p := Measure.infinitePi_map_eval _ _
    rw [← integral_map (measurable_pi_apply 0).aemeasurable hH1.aestronglyMeasurable, hm]
    have hi0 : Integrable H1 ((1-p) • Measure.dirac false) := (integrable_dirac (by simp)).smul_measure (ne_of_lt (lt_of_le_of_lt tsub_le_self (by simp)))
    have hi1 : Integrable H1 (p • Measure.dirac true) := (integrable_dirac (by simp)).smul_measure (ne_of_lt (lt_of_le_of_lt hp (by simp)))
    rw [show bitLaw p = (1-p) • Measure.dirac false + p • Measure.dirac true from rfl, integral_add_measure hi0 hi1]
    simp [integral_smul_measure, integral_dirac, H1, p, hθ0]
  have hZ0exp : (∫ ω : Tape, Z0 (shift ω) ∂μ) = ∫ ω : Tape, Z0 ω ∂μ := by
    rw [← integral_map hshift.aemeasurable hZ0.aestronglyMeasurable, hmap]
  have hZ1exp : (∫ ω : Tape, Z1 (shift ω) ∂μ) = ∫ ω : Tape, Z1 ω ∂μ := by
    rw [← integral_map hshift.aemeasurable hZ1.aestronglyMeasurable, hmap]
  have hprod0 := hInd0.integral_mul_eq_mul_integral (hH0.comp (measurable_pi_apply 0)).aestronglyMeasurable (hZ0.comp hshift).aestronglyMeasurable
  have hprod1 := hInd1.integral_mul_eq_mul_integral (hH1.comp (measurable_pi_apply 0)).aestronglyMeasurable (hZ1.comp hshift).aestronglyMeasurable
  change (∫ ω : Tape, H0 (ω 0) * Z0 (shift ω) ∂μ) = (∫ ω : Tape, H0 (ω 0) ∂μ) * (∫ ω : Tape, Z0 (shift ω) ∂μ) at hprod0
  change (∫ ω : Tape, H1 (ω 0) * Z1 (shift ω) ∂μ) = (∫ ω : Tape, H1 (ω 0) ∂μ) * (∫ ω : Tape, Z1 (shift ω) ∂μ) at hprod1
  rw [hH0exp, hZ0exp] at hprod0
  rw [hH1exp, hZ1exp] at hprod1
  have hBound0 : ∀ᵐ ω ∂μ, ‖H0 (ω 0)‖ ≤ (1:ℝ) := by
    filter_upwards with ω
    cases hb : ω 0 <;> simp [H0,hb]
  have hBound1 : ∀ᵐ ω ∂μ, ‖H1 (ω 0)‖ ≤ (1:ℝ) := by
    filter_upwards with ω
    cases hb : ω 0 <;> simp [H1,hb]
  have hP0 : Integrable (fun ω : Tape => H0 (ω 0) * Z0 (shift ω)) μ :=
    hZ0tail.bdd_mul (hH0.comp (measurable_pi_apply 0)).aestronglyMeasurable hBound0
  have hP1 : Integrable (fun ω : Tape => H1 (ω 0) * Z1 (shift ω)) μ :=
    hZ1tail.bdd_mul (hH1.comp (measurable_pi_apply 0)).aestronglyMeasurable hBound1
  have hpiece : ∀ᵐ ω ∂μ, z ^ upwardCount ω i = H0 (ω 0) * Z0 (shift ω) + z*(H1 (ω 0) * Z1 (shift ω)) := by
    filter_upwards [htail (i-1), htail (i+2)] with ω ht0 ht1
    have ht : ∃ t, level (shift ω) (if ω 0 then i+2 else i-1) t = 0 := by
      cases hb : ω 0 <;> simp [hb, ht0, ht1]
    have hc := upward_count_first_step ω i hi ht
    change upwardCount ω i = (if ω 0 then 1 else 0) + upwardCount (shift ω) (if ω 0 then i+2 else i-1) at hc
    cases hb : ω 0 <;> simp [hb, H0,H1,Z0,Z1,hc, pow_add, pow_succ, mul_comm, mul_left_comm, mul_assoc]
  change (∫ ω : Tape, z ^ upwardCount ω i ∂μ) = (1-θ)*(∫ ω : Tape, Z0 ω ∂μ) + θ*z*(∫ ω : Tape, Z1 ω ∂μ)
  calc
    _ = ∫ ω : Tape, (H0 (ω 0) * Z0 (shift ω) + z*(H1 (ω 0) * Z1 (shift ω))) ∂μ := integral_congr_ae hpiece
    _ = (∫ ω : Tape, H0 (ω 0) * Z0 (shift ω) ∂μ) + z*(∫ ω : Tape, H1 (ω 0) * Z1 (shift ω) ∂μ) := by
      rw [integral_add hP0 (hP1.const_mul z), integral_const_mul]
    _ = _ := by rw [hprod0, hprod1]; ring
