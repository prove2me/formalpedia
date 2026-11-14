-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.oracle_cost_eq_query_steps
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:28:09.294097+00:00
-- url     : https://prove2.me/submissions/ba31e9c9-2ea4-4962-9d38-1080e2a4bdf5

import Definitions.Def_CountingLLL_ReciprocalTest
import Theorems.Thm_CountingLLL_ReciprocalTest_oracle_progress
set_option autoImplicit false
open MeasureTheory CountingLLL.ReciprocalTest
open scoped ENNReal BigOperators

private def oracleInc (s : State) : ℕ := match s.phase with | .coinOracle _ => 1 | _ => 0
private def fairInc (s : State) : ℕ := match s.phase with | .start | .initialCheck | .coinFair _ => 1 | _ => 0
private def uniformInc (s : State) : ℕ := match s.phase with | .uniformCheck => 1 | _ => 0

private theorem counts_step (ω : Entropy) (s : State) :
    (step ω s).oracleUsed = s.oracleUsed + oracleInc s ∧
    (step ω s).fairUsed = s.fairUsed + fairInc s ∧
    (step ω s).uniformUsed = s.uniformUsed + uniformInc s := by
  cases hp : s.phase with
  | start => simp only [CountingLLL.ReciprocalTest.step, hp]; split <;> simp [oracleInc, fairInc, uniformInc, hp]
  | initialCheck => simp only [CountingLLL.ReciprocalTest.step, hp]; split <;> simp [oracleInc, fairInc, uniformInc, hp]
  | loop => simp only [CountingLLL.ReciprocalTest.step, hp]; split <;> simp [oracleInc, fairInc, uniformInc, hp]
  | coinOracle k =>
    cases k <;> simp only [CountingLLL.ReciprocalTest.step, hp] <;> split <;> simp [coinReturn, oracleInc, fairInc, uniformInc, hp]
  | coinFair k =>
    cases k <;> simp only [CountingLLL.ReciprocalTest.step, hp] <;> split <;> simp [coinReturn, oracleInc, fairInc, uniformInc, hp]
  | uniformCheck => simp only [CountingLLL.ReciprocalTest.step, hp]; split <;> simp [oracleInc, fairInc, uniformInc, hp]
  | done b => simp [CountingLLL.ReciprocalTest.step, hp, oracleInc, fairInc, uniformInc]


private theorem oracle_count (ω : Entropy) (n : ℕ) :
    (run ω n).oracleUsed = ∑ t ∈ Finset.range n, oracleInc (run ω t) := by
  induction n with
  | zero => simp [run, initial]
  | succ n ih =>
    have hr : run ω (n+1) = step ω (run ω n) := by simp [run, Function.iterate_succ_apply']
    rw [hr, (counts_step ω (run ω n)).1, Finset.sum_range_succ, ih]

private theorem oracle_infinite_of_nonhalt (ω : Entropy) (h : ¬ Halts ω) :
    (∑' t, (oracleInc (run ω t) : ℝ≥0∞)) = ⊤ := by
  apply top_unique
  rw [← ENNReal.iSup_natCast]
  apply iSup_le
  intro k
  let n := 4*k+1
  have hlive : (run ω n).phase ≠ .done false ∧ (run ω n).phase ≠ .done true := by
    constructor
    · intro hf; exact h ⟨n,false,hf⟩
    · intro ht; exact h ⟨n,true,ht⟩
  have hp := oracle_progress ω n hlive
  have hkn : k ≤ (run ω n).oracleUsed := by dsimp [n] at hp ⊢; omega
  have hpartial : ((run ω n).oracleUsed : ℝ≥0∞) = ∑ t ∈ Finset.range n, (oracleInc (run ω t) : ℝ≥0∞) := by
    rw [oracle_count]
    push_cast
    rfl
  calc
    (k : ℝ≥0∞) ≤ ((run ω n).oracleUsed : ℝ≥0∞) := by exact_mod_cast hkn
    _ = _ := hpartial
    _ ≤ ∑' t, (oracleInc (run ω t) : ℝ≥0∞) := ENNReal.sum_le_tsum _

/-- Total operational oracle cost equals the number of oracle-query steps, including nontermination. -/
private theorem oracle_cost_eq_visits (ω : Entropy) :
    oracleCost ω = ∑' t, (oracleInc (run ω t) : ℝ≥0∞) := by
  classical
  by_cases h : Halts ω
  · obtain ⟨b,hb⟩ := Nat.find_spec h
    have hfixed : step ω (run ω (Nat.find h)) = run ω (Nat.find h) := by
      rw [step, hb]
    have hafter (m : ℕ) : run ω (Nat.find h + m) = run ω (Nat.find h) := by
      change (step ω)^[Nat.find h + m] initial = _
      rw [Nat.add_comm, Function.iterate_add_apply]
      induction m with
      | zero => rfl
      | succ m ih => rw [Function.iterate_succ_apply', ih, hfixed]
    unfold oracleCost
    rw [dif_pos h, tsum_eq_sum (s := Finset.range (Nat.find h))]
    · rw [oracle_count]
      push_cast
      rfl
    · intro t ht
      have hle : Nat.find h ≤ t := Nat.le_of_not_gt (fun hh => ht (Finset.mem_range.mpr hh))
      obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [hafter]
      have hi : oracleInc (run ω (Nat.find h)) = 0 := by rw [oracleInc, hb]
      rw [hi]
      simp
  · rw [oracleCost, dif_neg h, oracle_infinite_of_nonhalt ω h]

theorem solution (ω : Entropy) :
    oracleCost ω = ∑' t, (match (run ω t).phase with | .coinOracle _ => (1:ℝ≥0∞) | _ => 0) := by
  rw [oracle_cost_eq_visits]
  apply tsum_congr
  intro t
  cases hp : (run ω t).phase <;> simp [oracleInc, hp]
