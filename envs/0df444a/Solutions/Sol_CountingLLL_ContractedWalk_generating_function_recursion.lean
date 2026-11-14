-- Prove2me | solution 1 for CountingLLL.ContractedWalk.generating_function_recursion
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:05:03.588209+00:00
-- url     : https://prove2.me/submissions/96885d5e-889d-4110-a34a-46a3864ff6b5

import Theorems.Thm_CountingLLL_ContractedWalk_first_step_expectation
import Definitions.Def_CountingLLL_ContractedGF
import Theorems.Thm_CountingLLL_ContractedWalk_upward_count_segment
import Theorems.Thm_CountingLLL_ContractedWalk_iid_ae_strong_markov
import Theorems.Thm_CountingLLL_ContractedWalk_upward_count_measurable_integrable
import Theorems.Thm_CountingLLL_ContractedWalk_absorption_and_expected_changes

set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ContractedWalk
open scoped ENNReal BigOperators

noncomputable section

local instance : MeasurableSpace (Option ℕ) := ⊤
local instance : DiscreteMeasurableSpace (Option ℕ) := ⟨fun _ => trivial⟩

private def τ (ω : Tape) : Option ℕ := by
  classical
  exact if h : ∃ t, level ω 1 t = 0 then some (Nat.find h) else none

private theorem level_ext' (ω ω' : Tape) (i t : ℕ) (h : ∀ k < t, ω k = ω' k) : level ω i t = level ω' i t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hprev : ∀ k < t, ω k = ω' k := by intro k hk; exact h k (by omega)
    have hnow := h t (by omega)
    simp only [level, ih hprev, hnow]

private theorem τ_spec (ω : Tape) (n : ℕ) : τ ω = some n ↔ level ω 1 n = 0 ∧ ∀ j < n, level ω 1 j ≠ 0 := by
  classical
  by_cases h : ∃ t, level ω 1 t = 0
  · simpa [τ,h] using (Nat.find_eq_iff h (m := n))
  · have hh : level ω 1 n ≠ 0 := by intro hn; exact h ⟨n,hn⟩
    simp [τ,h,hh]

private theorem τ_stopping (n : ℕ) (ω ω' : Tape) (h : ∀ k < n, ω k = ω' k) : τ ω = some n ↔ τ ω' = some n := by
  rw [τ_spec,τ_spec]
  have heq : level ω 1 n = level ω' 1 n := level_ext' ω ω' 1 n h
  have heq' : ∀ j < n, level ω 1 j = level ω' 1 j := by
    intro j hj
    exact level_ext' ω ω' 1 j (fun k hk => h k (by omega))
  constructor
  · rintro ⟨ht, hm⟩
    refine ⟨heq.symm.trans ht, ?_⟩
    intro j hj
    rw [← heq' j hj]
    exact hm j hj
  · rintro ⟨ht, hm⟩
    refine ⟨heq.trans ht, ?_⟩
    intro j hj
    rw [heq' j hj]
    exact hm j hj

private theorem stop_eq_of_τ (ω : Tape) (n : ℕ) (h : τ ω = some n) : stopTime ω 1 = n := by
  classical
  have hs := (τ_spec ω n).mp h
  have hh : ∃ t, level ω 1 t = 0 := ⟨n,hs.1⟩
  have hf : Nat.find hh = n := (Nat.find_eq_iff hh).mpr hs
  unfold stopTime
  rw [dif_pos hh, hf]

private theorem R_stopped (n : ℕ) (ω ω' : Tape) (h : ∀ k < n, ω k = ω' k) (ht : τ ω = some n) :
    upwardCount ω 1 = upwardCount ω' 1 := by
  classical
  have ht' : τ ω' = some n := (τ_stopping n ω ω' h).1 ht
  have hs := stop_eq_of_τ ω n ht
  have hs' := stop_eq_of_τ ω' n ht'
  unfold upwardCount
  rw [hs,hs']
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have he := level_ext' ω ω' 1 k (fun j hj => h j (by omega))
  rw [he,h k hk']

private theorem τ_some_meas (n : ℕ) : MeasurableSet {ω : Tape | τ ω = some n} := by
  classical
  let pref : Tape → (Fin n → Bool) := fun ω j => ω j.val
  have hm : Measurable pref := measurable_pi_lambda _ (fun j => measurable_pi_apply j.val)
  let F : Set (Fin n → Bool) := {x | ∃ ω : Tape, pref ω = x ∧ τ ω = some n}
  have heq : pref ⁻¹' F = {ω : Tape | τ ω = some n} := by
    ext ω
    constructor
    · rintro ⟨ω',heq,ht⟩
      have hpre : ∀ k < n, ω k = ω' k := by intro k hk; exact (congrFun heq ⟨k,hk⟩).symm
      exact (τ_stopping n ω ω' hpre).2 ht
    · intro ht; exact ⟨ω,rfl,ht⟩
  rw [←heq]
  exact MeasurableSet.of_discrete.preimage hm

private theorem τ_none_meas : MeasurableSet {ω : Tape | τ ω = none} := by
  have heq : {ω : Tape | τ ω = none} = (⋃ n : ℕ, {ω : Tape | τ ω = some n})ᶜ := by
    ext ω
    cases ht : τ ω <;> simp [ht]
  rw [heq]
  exact (MeasurableSet.iUnion τ_some_meas).compl

private theorem τ_meas : Measurable τ := by
  classical
  intro A hA
  have heq : τ ⁻¹' A = (if none ∈ A then {ω : Tape | τ ω = none} else ∅) ∪
      ⋃ n : ℕ, if some n ∈ A then {ω : Tape | τ ω = some n} else ∅ := by
    ext ω
    cases ht : τ ω <;> simp [ht]
  rw [heq]
  have h0 : MeasurableSet (if none ∈ A then {ω : Tape | τ ω = none} else ∅) := by
    by_cases h : none ∈ A
    · simpa only [if_pos h] using τ_none_meas
    · simp [h]
  apply h0.union
  apply MeasurableSet.iUnion
  intro n
  by_cases h : some n ∈ A
  · simpa only [if_pos h] using τ_some_meas n
  · simp [h]

private theorem random_tail_meas : Measurable (fun ω : Tape => fun k => ω (k+(τ ω).getD 0)) := by
  have hτn : Measurable (fun ω : Tape => (τ ω).getD 0) := (measurable_of_countable (fun o : Option ℕ => o.getD 0)).comp τ_meas
  apply measurable_pi_lambda
  intro k
  have heval : Measurable (fun x : ℕ × Tape => x.2 (k+x.1)) :=
    measurable_from_prod_countable_right (fun n => measurable_pi_apply (k+n))
  exact heval.comp (hτn.prodMk measurable_id)

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


private theorem bitLaw_probability' (p : ℝ≥0∞) (hp : p ≤ 1) : IsProbabilityMeasure (bitLaw p) := by
  constructor
  simp only [bitLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact tsub_add_cancel_of_le hp

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

private theorem factor_expectation (θ z : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 1/3)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (m : ℕ) :
    (∫ ω : Tape, z ^ upwardCount ω (m+1) ∂tapeLaw (ENNReal.ofReal θ)) =
      (∫ ω : Tape, z ^ upwardCount ω 1 ∂tapeLaw (ENNReal.ofReal θ)) *
      (∫ ω : Tape, z ^ upwardCount ω m ∂tapeLaw (ENNReal.ofReal θ)) := by
  classical
  let p := ENNReal.ofReal θ
  have hp : p ≤ 1 := by
    have hreal : θ ≤ (1:ℝ) := by linarith
    simpa [p] using ENNReal.ofReal_le_ofReal hreal
  letI : IsProbabilityMeasure (bitLaw p) := bitLaw_probability' p hp
  let μ := tapeLaw p
  letI : IsProbabilityMeasure μ := by dsimp [μ,tapeLaw]; infer_instance
  have hfin : ∀ᵐ ω ∂μ, τ ω ≠ none := by
    filter_upwards [ae_stop θ hθ0 hθ 1] with ω hstop
    simp [τ,hstop]
  let R : Tape → ℕ := fun ω => upwardCount ω 1
  let tail : Tape → Tape := fun ω k => ω (k+(τ ω).getD 0)
  have htail : Measurable tail := random_tail_meas
  have hSM := iid_ae_strong_markov p hp τ R τ_stopping R_stopped hfin
  have hmap : μ.map tail = μ := by
    ext A hA
    rw [Measure.map_apply htail hA]
    exact hSM.2 A hA
  let Z0 : ℕ → ℝ := fun n => z^n
  let Z1 : Tape → ℝ := fun ω => z ^ upwardCount ω m
  have hZ0 : Measurable Z0 := measurable_of_countable Z0
  have hZ1 : Measurable Z1 := (upward_count_measurable_integrable.1 m).const_pow z
  have hR : Measurable R := upward_count_measurable_integrable.1 1
  have hRint : Integrable (Z0 ∘ R) μ := upward_count_measurable_integrable.2 θ z (by linarith) hz0 hz1 1
  have hZ1int : Integrable Z1 μ := upward_count_measurable_integrable.2 θ z (by linarith) hz0 hz1 m
  have hTailInt : Integrable (Z1 ∘ tail) μ := by
    have hh := hZ1int
    rw [←hmap] at hh
    exact hh.comp_measurable htail
  have hInd := hSM.1.comp hZ0 hZ1
  have hprod := hInd.integral_mul_eq_mul_integral (hZ0.comp hR).aestronglyMeasurable (hZ1.comp htail).aestronglyMeasurable
  change (∫ ω : Tape, Z0 (R ω) * Z1 (tail ω) ∂μ) = (∫ ω : Tape, Z0 (R ω) ∂μ) * (∫ ω : Tape, Z1 (tail ω) ∂μ) at hprod
  have hTailExp : (∫ ω : Tape, Z1 (tail ω) ∂μ) = ∫ ω : Tape, Z1 ω ∂μ := by
    rw [← integral_map htail.aemeasurable hZ1.aestronglyMeasurable, hmap]
  rw [hTailExp] at hprod
  have htailStop : ∀ᵐ ω ∂μ, ∃ t, level (tail ω) m t = 0 := by
    have hae := ae_stop θ hθ0 hθ m
    change ∀ᵐ ω ∂μ, ∃ t, level ω m t = 0 at hae
    rw [←hmap] at hae
    exact (ae_map_iff htail.aemeasurable (stop_meas' m)).1 hae
  have hpiece : ∀ᵐ ω ∂μ, z ^ upwardCount ω (m+1) = Z0 (R ω) * Z1 (tail ω) := by
    filter_upwards [ae_stop θ hθ0 hθ 1, htailStop] with ω hhit hrest
    have ht : (τ ω).getD 0 = stopTime ω 1 := by
      have hfind : stopTime ω 1 = Nat.find hhit := by unfold stopTime; rw [dif_pos hhit]
      rw [hfind]
      simp [τ,hhit]
    have hrest' : ∃ t, level (fun k => ω (k+stopTime ω 1)) m t = 0 := by simpa [tail,ht] using hrest
    have hc := upward_count_segment ω m hhit hrest'
    simp [Z0,Z1,R,tail,ht,hc,pow_add]
  change (∫ ω : Tape, z ^ upwardCount ω (m+1) ∂μ) = (∫ ω : Tape, Z0 (R ω) ∂μ) * (∫ ω : Tape, Z1 ω ∂μ)
  calc
    _ = ∫ ω : Tape, Z0 (R ω) * Z1 (tail ω) ∂μ := integral_congr_ae hpiece
    _ = _ := hprod

private theorem bitLaw_probability_cubic (p : ℝ≥0∞) (hp : p ≤ 1) : IsProbabilityMeasure (bitLaw p) := by
  constructor
  simp only [bitLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact tsub_add_cancel_of_le hp

private theorem count_zero (ω : Tape) : upwardCount ω 0 = 0 := by
  classical
  have h : ∃ t, level ω 0 t = 0 := ⟨0,rfl⟩
  have hf : Nat.find h = 0 := (Nat.find_eq_zero h).2 rfl
  have hs : stopTime ω 0 = 0 := by
    unfold stopTime
    rw [dif_pos h, hf]
  simp [upwardCount,hs]

theorem solution (θ z : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 1/3) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    generatingFunction θ z = 1-θ+θ*z*(generatingFunction θ z)^3 := by
  have hp : ENNReal.ofReal θ ≤ 1 := by
    have hreal : θ ≤ (1:ℝ) := by linarith
    simpa using ENNReal.ofReal_le_ofReal hreal
  letI : IsProbabilityMeasure (bitLaw (ENNReal.ofReal θ)) := bitLaw_probability_cubic _ hp
  letI : IsProbabilityMeasure (tapeLaw (ENNReal.ofReal θ)) := by unfold tapeLaw; infer_instance
  have hF0 : (∫ ω : Tape, z ^ upwardCount ω 0 ∂tapeLaw (ENNReal.ofReal θ)) = 1 := by simp [count_zero]
  have hF2 := factor_expectation θ z hθ0 hθ hz0 hz1 1
  have hF3 := factor_expectation θ z hθ0 hθ hz0 hz1 2
  norm_num only at hF2 hF3
  have hstep := first_step_expectation θ z hθ0 hθ hz0 hz1 1 (by omega)
  norm_num only at hstep
  rw [hF0, hF3, hF2] at hstep
  dsimp [generatingFunction]
  nlinarith
