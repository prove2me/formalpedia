-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.coin_success_iff
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:58:26.485208+00:00
-- url     : https://prove2.me/submissions/a43d1ad7-39c9-4c66-8a47-953a19fbbfe6

import Definitions.Def_CountingLLL_ReciprocalTest

open CountingLLL.ReciprocalTest

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

private def Escaped (s : State) : Prop :=
  s.phase ≠ .start ∧ s.phase ≠ .coinOracle .initial ∧ s.phase ≠ .coinFair .initial ∧ s.phase ≠ .initialCheck

private theorem escaped_step (ω : Entropy) (s : State) (hs : Escaped s) : Escaped (step ω s) := by
  cases hp : s.phase with
  | start => simp [Escaped, hp] at hs
  | initialCheck => simp [Escaped, hp] at hs
  | loop => simp only [step, hp]; split <;> simp [Escaped]
  | coinOracle k =>
    cases k <;> simp_all [Escaped, step, coinReturn] <;> split <;> simp_all
  | coinFair k =>
    cases k <;> simp_all [Escaped, step, coinReturn] <;> split <;> simp_all
  | uniformCheck => simp only [step, hp]; split <;> simp [Escaped]
  | done b => simp [step, hp]; exact hs

private theorem escaped_iterate (ω : Entropy) (s : State) (hs : Escaped s) (n : ℕ) :
    Escaped ((step ω)^[n] s) := by
  induction n with
  | zero => simpa using hs
  | succ n ih => rw [Function.iterate_succ_apply']; exact escaped_step ω _ ih

private theorem coin_converse_aux (ω : Entropy) (t : ℕ) : ∀ n : ℕ,
    ((step ω)^[t] (coinState n)).phase = .initialCheck →
    ∃ m ≥ n, (∀ k, n ≤ k → k < m → ω.1 k = false ∧ ω.2.1 k = false) ∧ ω.1 m = true := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
   cases t with
   | zero =>
    intro n h
    simp [coinState] at h
   | succ t =>
    intro n h
    by_cases ho : ω.1 n = true
    · exact ⟨n, le_rfl, by intro k hkn hkl; omega, ho⟩
    · have ho' : ω.1 n = false := Bool.eq_false_iff.mpr ho
      cases t with
      | zero => simp [coinState, step, Function.iterate_succ_apply', ho'] at h
      | succ t =>
        by_cases hf : ω.2.1 n = true
        · have he : Escaped ((step ω)^[2] (coinState n)) := by
            simp [coinState, step, Function.iterate_succ_apply', ho', hf, coinReturn, Escaped]
          have he' := escaped_iterate ω _ he t
          have ht : (step ω)^[t+2] (coinState n) = (step ω)^[t] ((step ω)^[2] (coinState n)) := by
            rw [Function.iterate_add_apply]
          have hbad : ((step ω)^[t] ((step ω)^[2] (coinState n))).phase = .initialCheck := by
            simpa [ht] using h
          exact False.elim (he'.2.2.2 hbad)
        · have hf' : ω.2.1 n = false := Bool.eq_false_iff.mpr hf
          have hn : ((step ω)^[t] (coinState (n+1))).phase = .initialCheck := by
            rw [← coin_continue ω n ho' hf', ← Function.iterate_add_apply]
            convert h using 1 <;> congr 2 <;> omega
          obtain ⟨m, hm, hp, hmTrue⟩ := ih t (by omega) (n+1) hn
          refine ⟨m, by omega, ?_, hmTrue⟩
          intro k hkn hkm
          by_cases hk : k = n
          · subst k; exact ⟨ho', hf'⟩
          · exact hp k (by omega) hkm

private theorem coin_path_iff (ω : Entropy) :
    (∃ t, ((step ω)^[t] (coinState 0)).phase = .initialCheck) ↔
    ∃ n, (∀ k < n, ω.1 k = false ∧ ω.2.1 k = false) ∧ ω.1 n = true := by
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨n, hn, hp, ho⟩ := coin_converse_aux ω t 0 ht
    exact ⟨n, fun k hk => hp k (Nat.zero_le _) hk, ho⟩
  · rintro ⟨n, hp, ho⟩
    exact ⟨2*n+1, coin_one_path ω n hp ho⟩


theorem solution (ω : Entropy) : (∃ t, ((step ω)^[t] ({phase := .coinOracle .initial} : State)).phase = .initialCheck) ↔ ∃ n, (∀ k < n, ω.1 k = false ∧ ω.2.1 k = false) ∧ ω.1 n = true := by
  simpa [coinState] using coin_path_iff ω
