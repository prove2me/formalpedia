-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.oracle_cost_expectation_eq_occupancy
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:29:20.765198+00:00
-- url     : https://prove2.me/submissions/7bd332f3-4d15-4378-a952-123d12e73c21

import Definitions.Def_CountingLLL_ReciprocalEncodedLaw
import Theorems.Thm_CountingLLL_ReciprocalTest_oracle_cost_eq_query_steps

set_option autoImplicit false
open MeasureTheory CountingLLL.ReciprocalTest
open scoped ENNReal

private theorem step_ext (ω ω' : Entropy) (s : State)
    (ho : ω.1 s.oracleUsed = ω'.1 s.oracleUsed)
    (hf : ω.2.1 s.fairUsed = ω'.2.1 s.fairUsed)
    (hu : ω.2.2 (s.j-1,s.uniformUsed) = ω'.2.2 (s.j-1,s.uniformUsed)) : step ω s = step ω' s := by
  cases h : s.phase <;> simp [step, h, ho, hf, hu]

private theorem step_bounds (ω : Entropy) (s : State) :
    (step ω s).oracleUsed ≤ s.oracleUsed+1 ∧
    (step ω s).fairUsed ≤ s.fairUsed+1 ∧
    (step ω s).uniformUsed ≤ s.uniformUsed+1 ∧
    (step ω s).j ≤ s.j+2 := by
  cases h : s.phase with
  | start => simp only [step, h]; split <;> simp
  | initialCheck => simp only [step, h]; split <;> simp
  | loop => simp only [step, h]; split <;> simp
  | coinOracle k => cases k <;> simp only [step, h] <;> split <;> simp [coinReturn]
  | coinFair k => cases k <;> simp only [step, h] <;> split <;> simp [coinReturn]
  | uniformCheck => simp only [step, h]; split <;> simp
  | done b => simp [step, h]

private theorem iterate_ext (ω ω' : Entropy) (t : ℕ) : ∀ s : State,
    (∀ i < s.oracleUsed+t, ω.1 i = ω'.1 i) →
    (∀ i < s.fairUsed+t, ω.2.1 i = ω'.2.1 i) →
    (∀ n < s.j+2*t+1, ∀ i < s.uniformUsed+t, ω.2.2 (n,i) = ω'.2.2 (n,i)) →
    (step ω)^[t] s = (step ω')^[t] s := by
  induction t with
  | zero => intro s ho hf hu; rfl
  | succ t ih =>
    intro s ho hf hu
    have hstep := step_ext ω ω' s (ho _ (by omega)) (hf _ (by omega)) (hu _ (by omega) _ (by omega))
    have hb := step_bounds ω s
    have ho' : ∀ i < (step ω s).oracleUsed+t, ω.1 i = ω'.1 i := by intro i hi; exact ho i (by omega)
    have hf' : ∀ i < (step ω s).fairUsed+t, ω.2.1 i = ω'.2.1 i := by intro i hi; exact hf i (by omega)
    have hu' : ∀ n < (step ω s).j+2*t+1, ∀ i < (step ω s).uniformUsed+t, ω.2.2 (n,i) = ω'.2.2 (n,i) := by
      intro n hn i hi
      exact hu n (by omega) i (by omega)
    simpa [Function.iterate_succ_apply, hstep] using ih (step ω s) ho' hf' hu'

private theorem finite_event (t : ℕ) (A : State → Prop) : MeasurableSet {ω : Entropy | A (run ω t)} := by
  classical
  let pref : Entropy → ((Fin t → Bool) × (Fin t → Bool) × ((q : Fin (2*t+1) × Fin t) → Fin (q.1.val+1))) :=
    fun ω => (fun i => ω.1 i.val, fun i => ω.2.1 i.val, fun q => ω.2.2 (q.1.val,q.2.val))
  have hm : Measurable pref := by
    apply Measurable.prodMk
    · exact measurable_pi_lambda _ (fun i => (measurable_pi_apply i.val).comp measurable_fst)
    · apply Measurable.prodMk
      · exact measurable_pi_lambda _ (fun i => (measurable_pi_apply i.val).comp (measurable_fst.comp measurable_snd))
      · exact measurable_pi_lambda _ (fun q => (measurable_pi_apply (q.1.val,q.2.val)).comp (measurable_snd.comp measurable_snd))
  let T := {p | ∃ ω : Entropy, A (run ω t) ∧ pref ω = p}
  have heq : {ω : Entropy | A (run ω t)} = pref ⁻¹' T := by
    ext ω
    constructor
    · intro hω; exact ⟨ω, hω, rfl⟩
    · rintro ⟨ω', hω', hpre⟩
      have ho : ∀ i < t, ω.1 i = ω'.1 i := by
        intro i hi
        exact (congrFun (congrArg Prod.fst hpre) ⟨i,hi⟩).symm
      have hf : ∀ i < t, ω.2.1 i = ω'.2.1 i := by
        intro i hi
        exact (congrFun (congrArg Prod.fst (congrArg Prod.snd hpre)) ⟨i,hi⟩).symm
      have hu : ∀ n < 2*t+1, ∀ i < t, ω.2.2 (n,i) = ω'.2.2 (n,i) := by
        intro n hn i hi
        exact (congrFun (congrArg Prod.snd (congrArg Prod.snd hpre)) (⟨n,hn⟩, ⟨i,hi⟩)).symm
      have hh := iterate_ext ω ω' t initial (by simpa [initial] using ho) (by simpa [initial] using hf) (by simpa [initial] using hu)
      simpa [run, hh] using hω'
  rw [heq]
  exact MeasurableSet.of_discrete.preimage hm


private def E (t : ℕ) : Set Entropy := {ω | ∃ k : Context, (run ω t).phase = .coinOracle k}

theorem solution (B : ℝ≥0∞) :
    ∫⁻ ω, oracleCost ω ∂(entropyLaw B) = ∑' t, entropyLaw B {ω | ∃ k : Context, (run ω t).phase = .coinOracle k} := by
  classical
  change ∫⁻ ω, oracleCost ω ∂(entropyLaw B) = ∑' t, entropyLaw B (E t)
  have hE (t : ℕ) : MeasurableSet (E t) := finite_event t (fun s => ∃ k : Context, s.phase = .coinOracle k)
  have heq (ω : Entropy) (t : ℕ) :
      (match (run ω t).phase with | .coinOracle _ => (1:ℝ≥0∞) | _ => 0) = (E t).indicator (fun _ => 1) ω := by
    cases hp : (run ω t).phase <;> simp [E, Set.indicator, hp]
  calc
    ∫⁻ ω, oracleCost ω ∂(entropyLaw B) = ∫⁻ ω, ∑' t, (E t).indicator (fun _ => 1) ω ∂(entropyLaw B) := by
      apply lintegral_congr
      intro ω
      rw [oracle_cost_eq_query_steps]
      exact tsum_congr (heq ω)
    _ = ∑' t, ∫⁻ ω, (E t).indicator (fun _ => 1) ω ∂(entropyLaw B) := by
      rw [lintegral_tsum (fun t => (measurable_const.indicator (hE t)).aemeasurable)]
    _ = ∑' t, entropyLaw B (E t) := by
      apply tsum_congr
      intro t
      exact lintegral_indicator_one (hE t)
