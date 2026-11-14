-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.coin_cost_geometric_all
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:26:50.442203+00:00
-- url     : https://prove2.me/submissions/482729c9-fae1-409a-9443-e52aa9b850f0

import Definitions.Def_CountingLLL_CoinCost
import Theorems.Thm_CountingLLL_ReciprocalTest_coin_first_return_and_cost
set_option autoImplicit false
open MeasureTheory CountingLLL.ReciprocalTest
open scoped ENNReal

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

private theorem prefix_phase (ω : Entropy) (n t : ℕ)
    (h : ∀ k < n, ω.1 k = false ∧ ω.2.1 k = false) (ht : t ≤ 2*n) :
    ((step ω)^[t] (coinState 0)).phase = .coinOracle .initial ∨
      ((step ω)^[t] (coinState 0)).phase = .coinFair .initial := by
  let k := t/2
  have hk : k ≤ n := by dsimp [k]; omega
  have hp : ∀ q < k, ω.1 q = false ∧ ω.2.1 q = false := by
    intro q hq; exact h q (by omega)
  have hf := coin_prefix ω k hp
  by_cases ht_even : t % 2 = 0
  · have heq : t = 2*k := by dsimp [k]; omega
    rw [heq, hf]
    exact Or.inl rfl
  · have heq : t = 2*k+1 := by dsimp [k]; omega
    have hklt : k < n := by omega
    rw [heq, Function.iterate_succ_apply', hf]
    have ho := (h k hklt).1
    simp [coinState, step, ho]


private theorem coin_exact_cost (ω : Entropy) (n : ℕ)
    (h : ∀ k < n, ω.1 k = false ∧ ω.2.1 k = false)
    (hexit : ω.1 n = true ∨ ω.2.1 n = true) :
    coinOracleCost ω = (n+1 : ℕ) := by
  obtain ⟨T, hT, hcost, hearlier⟩ := coin_first_return_and_cost ω n h hexit
  have hreturn : CoinReturned ω := ⟨T, hT⟩
  have heq : Nat.find hreturn = T := by
    apply Nat.le_antisymm (Nat.find_min' hreturn hT)
    by_contra hnot
    have hlt : Nat.find hreturn < T := by omega
    have hfirst := Nat.find_spec hreturn
    have hbad := hearlier _ hlt
    rcases hfirst with hc | hc
    · exact hbad.1 hc
    · exact hbad.2 hc
  simp [coinOracleCost, hreturn, heq, hcost]

/-- The operational cost equals the geometric trial count on every exiting tape. -/
private theorem coin_cost_geometric (ω : Entropy) (n : ℕ)
    (h : ∀ k < n, ω.1 k = false ∧ ω.2.1 k = false)
    (hexit : ω.1 n = true ∨ ω.2.1 n = true) :
    coinOracleCost ω = ∑' k : ℕ,
      ({x : ℕ → Bool × Bool | ∀ i < k, x i = (false,false)}).indicator
        (1 : (ℕ → Bool × Bool) → ℝ≥0∞) (fun i => (ω.1 i, ω.2.1 i)) := by
  rw [coin_exact_cost ω n h hexit]
  rw [tsum_eq_sum (s := Finset.range (n+1))]
  · have heq : (∑ k ∈ Finset.range (n+1),
        ({x : ℕ → Bool × Bool | ∀ i < k, x i = (false,false)}).indicator
          (1 : (ℕ → Bool × Bool) → ℝ≥0∞) (fun i => (ω.1 i, ω.2.1 i))) =
        ∑ _k ∈ Finset.range (n+1), (1 : ℝ≥0∞) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := by simpa using hk
      have hm : (fun i => (ω.1 i, ω.2.1 i)) ∈ {x : ℕ → Bool × Bool | ∀ i < k, x i = (false,false)} := by
        intro i hi
        exact Prod.ext (h i (by omega)).1 (h i (by omega)).2
      simp [hm]
    rw [heq]
    simp
  · intro k hk
    have hnk : n < k := by simpa using hk
    have hnmem : (fun i => (ω.1 i, ω.2.1 i)) ∉ {x : ℕ → Bool × Bool | ∀ i < k, x i = (false,false)} := by
      intro hall
      have hh := hall n hnk
      rcases hexit with ho | hf
      · have := congrArg Prod.fst hh; simp [ho] at this
      · have := congrArg Prod.snd hh; simp [hf] at this
    simp [hnmem]

/-- Operational first-return cost is exactly the IID geometric count, on all tapes. -/
theorem solution (ω : Entropy) :
    coinOracleCost ω = ∑' k : ℕ,
      ({x : ℕ → Bool × Bool | ∀ i < k, x i = (false,false)}).indicator
        (1 : (ℕ → Bool × Bool) → ℝ≥0∞) (fun i => (ω.1 i, ω.2.1 i)) := by
  classical
  by_cases hex : ∃ n, ω.1 n = true ∨ ω.2.1 n = true
  · let n := Nat.find hex
    have hn : ω.1 n = true ∨ ω.2.1 n = true := Nat.find_spec hex
    have hp : ∀ k < n, ω.1 k = false ∧ ω.2.1 k = false := by
      intro k hk
      have hne := Nat.find_min hex hk
      have ho : ω.1 k ≠ true := by intro h; exact hne (Or.inl h)
      have hf : ω.2.1 k ≠ true := by intro h; exact hne (Or.inr h)
      exact ⟨Bool.eq_false_iff.mpr ho, Bool.eq_false_iff.mpr hf⟩
    exact coin_cost_geometric ω n hp hn
  · have hp : ∀ k, ω.1 k = false ∧ ω.2.1 k = false := by
      intro k
      have ho : ω.1 k ≠ true := by intro h; exact hex ⟨k, Or.inl h⟩
      have hf : ω.2.1 k ≠ true := by intro h; exact hex ⟨k, Or.inr h⟩
      exact ⟨Bool.eq_false_iff.mpr ho, Bool.eq_false_iff.mpr hf⟩
    have hnret : ¬ CoinReturned ω := by
      rintro ⟨t, ht⟩
      have hphase := prefix_phase ω t t (by intro k hk; exact hp k) (by omega)
      change ((step ω)^[t] (coinState 0)).phase = .initialCheck ∨
        ((step ω)^[t] (coinState 0)).phase = .loop at ht
      rcases hphase with hphase | hphase <;> simp [hphase] at ht
    simp only [coinOracleCost, hnret, ↓reduceDIte]
    have heq (k : ℕ) :
      ({x : ℕ → Bool × Bool | ∀ i < k, x i = (false,false)}).indicator
        (1 : (ℕ → Bool × Bool) → ℝ≥0∞) (fun i => (ω.1 i, ω.2.1 i)) = 1 := by
      have hm : (fun i => (ω.1 i, ω.2.1 i)) ∈ {x : ℕ → Bool × Bool | ∀ i < k, x i = (false,false)} := by
        intro i hi; exact Prod.ext (hp i).1 (hp i).2
      simp [hm]
    simp only [heq]
    simp
