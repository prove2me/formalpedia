-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.coin_operational_stops
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:11:14.610914+00:00
-- url     : https://prove2.me/submissions/7077b5aa-f361-4562-94eb-69f7f81dfaad

import Definitions.Def_CountingLLL_ReciprocalTest
import Theorems.Thm_CountingLLL_ReciprocalTest_paired_streams
import Theorems.Thm_CountingLLL_RandomRAM_iid_first_exit

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


private def coinState (n : ℕ) : State := { phase := .coinOracle .initial, oracleUsed := n, fairUsed := n }

private theorem coin_continue (ω : Entropy) (n : ℕ) (ho : ω.1 n = false) (hf : ω.2.1 n = false) :
    (step ω)^[2] (coinState n) = coinState (n+1) := by
  simp [coinState, step, Function.iterate_succ_apply', ho, hf]

private theorem coin_prefix (ω : Entropy) (n : ℕ)
    (h : ∀ k < n, ω.1 k = false ∧ ω.2.1 k = false) :
    (step ω)^[2*n] (coinState 0) = coinState n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := h n (Nat.lt_succ_self n)
    have hprev : ∀ k < n, ω.1 k = false ∧ ω.2.1 k = false := by
      intro k hk; exact h k (Nat.lt.step hk)
    have hi := ih hprev
    rw [show 2 * (n + 1) = 2 + 2 * n by omega, Function.iterate_add_apply, hi]
    exact coin_continue ω n hn.1 hn.2

private theorem coin_one_path (ω : Entropy) (n : ℕ)
    (h : ∀ k < n, ω.1 k = false ∧ ω.2.1 k = false) (ho : ω.1 n = true) :
    ((step ω)^[2*n+1] (coinState 0)).phase = .initialCheck := by
  rw [Function.iterate_succ_apply', coin_prefix ω n h]
  simp [coinState, step, ho, coinReturn]

private theorem iid_exit_as {β : Type} [MeasurableSpace β] (ν : Measure β) [IsProbabilityMeasure ν]
    (S : Set β) (hS : MeasurableSet S) (hS1 : ν S < 1) :
    (Measure.infinitePi fun _ : ℕ => ν) {ω : ℕ → β | ∃ n, (∀ i < n, ω i ∈ S) ∧ ω n ∉ S} = 1 := by
  have hd : Disjoint S Sᶜ := Set.disjoint_left.mpr (by simp)
  have h := CountingLLL.RandomRAM.iid_first_exit ν S Sᶜ hS hS.compl hd
  have hfin : ν S ≠ ⊤ := ne_of_lt (hS1.trans_le (by simp))
  rw [measure_compl hS hfin, measure_univ] at h
  have hden0 : (1 : ℝ≥0∞) - ν S ≠ 0 := by
    exact ne_of_gt (tsub_pos_iff_lt.mpr hS1)
  have hdenT : (1 : ℝ≥0∞) - ν S ≠ ⊤ := ne_of_lt (lt_of_le_of_lt tsub_le_self (by simp))
  rw [ENNReal.div_self hden0 hdenT] at h
  exact h


theorem solution (B : ℝ) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) :
    entropyLaw (ENNReal.ofReal B)
      {ω | ∃ t, ((step ω)^[t] ({phase := .coinOracle .initial} : State)).phase = .initialCheck ∨
                 ((step ω)^[t] ({phase := .coinOracle .initial} : State)).phase = .loop} = 1 := by
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
  let ν := (oracleLaw p).prod fairLaw
  letI : IsProbabilityMeasure ν := inferInstance
  let S : Set (Bool × Bool) := {(false,false)}
  have hs : MeasurableSet S := MeasurableSet.singleton _
  have hsval : ν S = ENNReal.ofReal (B/2) := by
    have heq : S = ({false} : Set Bool) ×ˢ ({false} : Set Bool) := by ext ⟨a,b⟩; simp [S]
    rw [heq, Measure.prod_prod]
    simp [ν, oracleLaw, fairLaw, p, ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
    simp [div_eq_mul_inv]
  have hslt : ν S < 1 := by
    rw [hsval, ← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ) < 1)]
    linarith
  let E : Set (ℕ → Bool × Bool) := {x | ∃ n, (∀ i < n, x i ∈ S) ∧ x n ∉ S}
  have hE : MeasurableSet E := by
    have he : E = ⋃ n : ℕ, (⋂ i : Fin n, {x : ℕ → Bool × Bool | x i.val ∈ S}) ∩ {x | x n ∉ S} := by
      ext x
      simp only [E, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter]
      constructor
      · rintro ⟨n, hn, h⟩; exact ⟨n, fun i => hn i.val i.isLt, h⟩
      · rintro ⟨n, hn, h⟩; exact ⟨n, fun i hi => hn ⟨i, hi⟩, h⟩
    rw [he]
    exact MeasurableSet.iUnion fun n =>
      (MeasurableSet.iInter fun i => hs.preimage (measurable_pi_apply i.val)).inter (hs.compl.preimage (measurable_pi_apply n))
  have hone : entropyLaw p ((pair ∘ proj) ⁻¹' E) = 1 := by
    rw [← Measure.map_apply (hpair.comp hproj) hE, hmap]
    exact iid_exit_as ν S hs hslt
  have hsub : (pair ∘ proj) ⁻¹' E ⊆
      {ω : Entropy | ∃ t, ((step ω)^[t] ({phase := .coinOracle .initial} : State)).phase = .initialCheck ∨
                             ((step ω)^[t] ({phase := .coinOracle .initial} : State)).phase = .loop} := by
    intro ω hω
    obtain ⟨n, hpref, hlast⟩ := hω
    have hpref' : ∀ k < n, ω.1 k = false ∧ ω.2.1 k = false := by
      intro k hk
      have h := hpref k hk
      simpa [S, pair, proj, Prod.ext_iff] using h
    by_cases ho : ω.1 n = true
    · exact ⟨2*n+1, Or.inl (by simpa [coinState] using coin_one_path ω n hpref' ho)⟩
    · have ho' : ω.1 n = false := Bool.eq_false_iff.mpr ho
      have hf : ω.2.1 n = true := by
        cases hbit : ω.2.1 n <;> simp_all [S, pair, proj, Prod.ext_iff]
      refine ⟨2*n+2, Or.inr ?_⟩
      change ((step ω)^[2*n+2] (coinState 0)).phase = .loop
      rw [show 2*n+2 = 2+2*n by omega, Function.iterate_add_apply, coin_prefix ω n hpref']
      simp [coinState, step, Function.iterate_succ_apply', ho', hf, coinReturn]
  have hle : 1 ≤ entropyLaw p {ω : Entropy | ∃ t, ((step ω)^[t] ({phase := .coinOracle .initial} : State)).phase = .initialCheck ∨
                             ((step ω)^[t] ({phase := .coinOracle .initial} : State)).phase = .loop} := by
    rw [← hone]
    exact measure_mono hsub
  have hpmeasure : IsProbabilityMeasure (entropyLaw p) := by
    unfold entropyLaw
    infer_instance
  letI := hpmeasure
  apply le_antisymm _ hle
  simpa using (measure_mono (μ := entropyLaw p) (Set.subset_univ _))
