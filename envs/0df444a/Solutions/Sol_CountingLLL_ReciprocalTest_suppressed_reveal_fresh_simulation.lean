-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.suppressed_reveal_fresh_simulation
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:57:16.071681+00:00
-- url     : https://prove2.me/submissions/ea8adb7f-3d11-484e-a449-2c4be38028c5

import Definitions.Def_CountingLLL_ReciprocalSuppressedReveal
set_option autoImplicit false
open CountingLLL.ReciprocalTest CountingLLL.RevealMachine

private theorem sim_step (ω : Entropy) (s : State) (S : Finset ReadIndex) :
    (CountingLLL.RevealMachine.step suppressedRevealProgram (entropyCode ω) (s,S)).1 = allSuppressedStep ω s := by
  cases hs : s.phase <;> simp [CountingLLL.RevealMachine.step, suppressedRevealProgram, readIndex,
    allSuppressedStep, suppressedStep, CountingLLL.ReciprocalTest.step, hs, entropyCode, uniformEntropy]
  all_goals split <;> simp_all

private theorem suppressed_reveal_simulates (ω : Entropy) (n : ℕ) :
    (CountingLLL.RevealMachine.run suppressedRevealProgram (entropyCode ω) initial n).1 =
      allSuppressedRun ω n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hr : CountingLLL.RevealMachine.run suppressedRevealProgram (entropyCode ω) initial (n+1) =
        CountingLLL.RevealMachine.step suppressedRevealProgram (entropyCode ω)
          (CountingLLL.RevealMachine.run suppressedRevealProgram (entropyCode ω) initial n) := by
      simp [CountingLLL.RevealMachine.run, Function.iterate_succ_apply']
    have hc : allSuppressedRun ω (n+1) = allSuppressedStep ω (allSuppressedRun ω n) := by
      simp [allSuppressedRun, Function.iterate_succ_apply']
    rw [hr, hc, ← ih]
    exact sim_step ω _ _

private def oracleInc (s : State) : ℕ := match s.phase with | .coinOracle _ => 1 | _ => 0
private def fairInc (s : State) : ℕ := match s.phase with | .start | .initialCheck | .coinFair _ => 1 | _ => 0
private def uniformInc (s : State) : ℕ := match s.phase with | .uniformCheck => 1 | _ => 0

private theorem counts_step (ω : Entropy) (s : State) :
    (allSuppressedStep ω s).oracleUsed = s.oracleUsed + oracleInc s ∧
    (allSuppressedStep ω s).fairUsed = s.fairUsed + fairInc s ∧
    (allSuppressedStep ω s).uniformUsed = s.uniformUsed + uniformInc s := by
  cases hp : s.phase with
  | start => simp [allSuppressedStep, oracleInc, fairInc, uniformInc, hp]
  | initialCheck => simp [allSuppressedStep, suppressedStep, oracleInc, fairInc, uniformInc, hp]
  | loop => simp only [allSuppressedStep, suppressedStep, CountingLLL.ReciprocalTest.step, hp]; split <;> simp [oracleInc, fairInc, uniformInc, hp]
  | coinOracle k =>
    cases k <;> simp only [allSuppressedStep, suppressedStep, CountingLLL.ReciprocalTest.step, hp] <;> split <;> simp [coinReturn, oracleInc, fairInc, uniformInc, hp]
  | coinFair k =>
    cases k <;> simp only [allSuppressedStep, suppressedStep, CountingLLL.ReciprocalTest.step, hp] <;> split <;> simp [coinReturn, oracleInc, fairInc, uniformInc, hp]
  | uniformCheck => simp [allSuppressedStep, suppressedStep, oracleInc, fairInc, uniformInc, hp]
  | done b => simp [allSuppressedStep, suppressedStep, CountingLLL.ReciprocalTest.step, hp, oracleInc, fairInc, uniformInc]

private def FreshInv (c : State × Finset ReadIndex) : Prop :=
  (∀ k, .inl k ∈ c.2 → k < c.1.oracleUsed) ∧
  (∀ k, .inr (.inl k) ∈ c.2 → k < c.1.fairUsed) ∧
  (∀ a, .inr (.inr a) ∈ c.2 → a.2 < c.1.uniformUsed)

private theorem inv_silent (s s' : State) (S : Finset ReadIndex) (h : FreshInv (s,S))
    (ho : s'.oracleUsed = s.oracleUsed) (hf : s'.fairUsed = s.fairUsed)
    (hu : s'.uniformUsed = s.uniformUsed) : FreshInv (s',S) := by
  simpa [FreshInv, ho, hf, hu] using h

private theorem inv_oracle (s s' : State) (S : Finset ReadIndex) (h : FreshInv (s,S))
    (ho : s'.oracleUsed = s.oracleUsed+1) (hf : s'.fairUsed = s.fairUsed)
    (hu : s'.uniformUsed = s.uniformUsed) : FreshInv (s',insert (.inl s.oracleUsed) S) := by
  simp only [FreshInv, Prod.fst, Prod.snd] at h ⊢
  rcases h with ⟨h1,h2,h3⟩
  constructor
  · intro k hk; simp only [Finset.mem_insert, Sum.inl.injEq] at hk
    rcases hk with rfl | hk
    · omega
    · have := h1 k hk; omega
  constructor
  · intro k hk; simp only [Finset.mem_insert, Sum.inr_ne_inl, false_or] at hk
    simpa [hf] using h2 k hk
  · intro a hk; simp only [Finset.mem_insert, Sum.inr_ne_inl, false_or] at hk
    simpa [hu] using h3 a hk

private theorem inv_fair (s s' : State) (S : Finset ReadIndex) (h : FreshInv (s,S))
    (ho : s'.oracleUsed = s.oracleUsed) (hf : s'.fairUsed = s.fairUsed+1)
    (hu : s'.uniformUsed = s.uniformUsed) : FreshInv (s',insert (.inr (.inl s.fairUsed)) S) := by
  simp only [FreshInv, Prod.fst, Prod.snd] at h ⊢
  rcases h with ⟨h1,h2,h3⟩
  constructor
  · intro k hk; simp only [Finset.mem_insert, Sum.inl_ne_inr, false_or] at hk
    simpa [ho] using h1 k hk
  constructor
  · intro k hk; simp only [Finset.mem_insert, Sum.inr.injEq, Sum.inl.injEq] at hk
    rcases hk with rfl | hk
    · omega
    · have := h2 k hk; omega
  · intro a hk; simp only [Finset.mem_insert, Sum.inr.injEq, Sum.inr_ne_inl, false_or] at hk
    simpa [hu] using h3 a hk

private theorem inv_uniform (s s' : State) (S : Finset ReadIndex) (h : FreshInv (s,S))
    (ho : s'.oracleUsed = s.oracleUsed) (hf : s'.fairUsed = s.fairUsed)
    (hu : s'.uniformUsed = s.uniformUsed+1) : FreshInv (s',insert (.inr (.inr (s.j-1,s.uniformUsed))) S) := by
  simp only [FreshInv, Prod.fst, Prod.snd] at h ⊢
  rcases h with ⟨h1,h2,h3⟩
  constructor
  · intro k hk; simp only [Finset.mem_insert, Sum.inl_ne_inr, false_or] at hk
    simpa [ho] using h1 k hk
  constructor
  · intro k hk; simp only [Finset.mem_insert, Sum.inr.injEq, Sum.inl_ne_inr, false_or] at hk
    simpa [hf] using h2 k hk
  · intro a hk; simp only [Finset.mem_insert, Sum.inr.injEq] at hk
    rcases hk with h | hk
    · subst a; simp [hu]
    · have := h3 a hk; omega

private theorem invariant_step (x : ReadIndex → ℕ) (s : State) (S : Finset ReadIndex)
    (h : FreshInv (s,S)) : FreshInv (CountingLLL.RevealMachine.step suppressedRevealProgram x (s,S)) := by
  cases hp : s.phase with
  | start =>
    have hc := counts_step (uniformEntropy (x (.inr (.inl s.fairUsed)))) s
    simp only [oracleInc, fairInc, uniformInc, hp, Nat.add_zero] at hc
    simpa [CountingLLL.RevealMachine.step, suppressedRevealProgram, readIndex, hp] using inv_fair s _ S h hc.1 hc.2.1 hc.2.2
  | initialCheck =>
    have hc := counts_step (uniformEntropy (x (.inr (.inl s.fairUsed)))) s
    simp only [oracleInc, fairInc, uniformInc, hp, Nat.add_zero] at hc
    simpa [CountingLLL.RevealMachine.step, suppressedRevealProgram, readIndex, hp] using inv_fair s _ S h hc.1 hc.2.1 hc.2.2
  | loop =>
    have hc := counts_step (uniformEntropy 0) s
    simp only [oracleInc, fairInc, uniformInc, hp, Nat.add_zero] at hc
    simpa [CountingLLL.RevealMachine.step, suppressedRevealProgram, readIndex, hp] using inv_silent s _ S h hc.1 hc.2.1 hc.2.2
  | coinOracle k =>
    have hc := counts_step (uniformEntropy (x (.inl s.oracleUsed))) s
    simp only [oracleInc, fairInc, uniformInc, hp, Nat.add_zero] at hc
    simpa [CountingLLL.RevealMachine.step, suppressedRevealProgram, readIndex, hp] using inv_oracle s _ S h hc.1 hc.2.1 hc.2.2
  | coinFair k =>
    have hc := counts_step (uniformEntropy (x (.inr (.inl s.fairUsed)))) s
    simp only [oracleInc, fairInc, uniformInc, hp, Nat.add_zero] at hc
    simpa [CountingLLL.RevealMachine.step, suppressedRevealProgram, readIndex, hp] using inv_fair s _ S h hc.1 hc.2.1 hc.2.2
  | uniformCheck =>
    have hc := counts_step (uniformEntropy (x (.inr (.inr (s.j-1,s.uniformUsed))))) s
    simp only [oracleInc, fairInc, uniformInc, hp, Nat.add_zero] at hc
    simpa [CountingLLL.RevealMachine.step, suppressedRevealProgram, readIndex, hp] using inv_uniform s _ S h hc.1 hc.2.1 hc.2.2
  | done b =>
    have hc := counts_step (uniformEntropy 0) s
    simp only [oracleInc, fairInc, uniformInc, hp, Nat.add_zero] at hc
    simpa [CountingLLL.RevealMachine.step, suppressedRevealProgram, readIndex, hp] using inv_silent s _ S h hc.1 hc.2.1 hc.2.2

private theorem invariant_run (x : ReadIndex → ℕ) (n : ℕ) :
    FreshInv (CountingLLL.RevealMachine.run suppressedRevealProgram x initial n) := by
  induction n with
  | zero => simp [CountingLLL.RevealMachine.run, FreshInv]
  | succ n ih =>
    have hr : CountingLLL.RevealMachine.run suppressedRevealProgram x initial (n+1) =
        CountingLLL.RevealMachine.step suppressedRevealProgram x (CountingLLL.RevealMachine.run suppressedRevealProgram x initial n) := by
      simp [CountingLLL.RevealMachine.run, Function.iterate_succ_apply']
    rw [hr]
    generalize hc : CountingLLL.RevealMachine.run suppressedRevealProgram x initial n = c at *
    obtain ⟨s,S⟩ := c
    exact invariant_step x s S ih

/-- Every query of the encoded ReciprocalTest uses an unseen coordinate. -/
private theorem suppressed_query_fresh (x : ReadIndex → ℕ) (n : ℕ) (a : ReadIndex)
    (h : readIndex (CountingLLL.RevealMachine.run suppressedRevealProgram x initial n).1 = some a) :
    a ∉ (CountingLLL.RevealMachine.run suppressedRevealProgram x initial n).2 := by
  have hinv := invariant_run x n
  let c := CountingLLL.RevealMachine.run suppressedRevealProgram x initial n
  change FreshInv c at hinv
  change readIndex c.1 = some a at h
  cases hp : c.1.phase with
  | start =>
    simp [readIndex, hp] at h
    subst a
    intro hm
    have := hinv.2.1 c.1.fairUsed hm
    omega
  | initialCheck =>
    simp [readIndex, hp] at h
    subst a
    intro hm
    have := hinv.2.1 c.1.fairUsed hm
    omega
  | loop => simp [readIndex, hp] at h
  | coinOracle k =>
    simp [readIndex, hp] at h
    subst a
    intro hm
    have := hinv.1 c.1.oracleUsed hm
    omega
  | coinFair k =>
    simp [readIndex, hp] at h
    subst a
    intro hm
    have := hinv.2.1 c.1.fairUsed hm
    omega
  | uniformCheck =>
    simp [readIndex, hp] at h
    subst a
    intro hm
    have := hinv.2.2 (c.1.j-1,c.1.uniformUsed) hm
    simp at this
  | done b => simp [readIndex, hp] at h


theorem solution :
    (∀ (ω : Entropy) (n : ℕ),
      (CountingLLL.RevealMachine.run suppressedRevealProgram (entropyCode ω) initial n).1 = allSuppressedRun ω n) ∧
    (∀ (x : ReadIndex → ℕ) (n : ℕ) (a : ReadIndex),
      readIndex (CountingLLL.RevealMachine.run suppressedRevealProgram x initial n).1 = some a →
      a ∉ (CountingLLL.RevealMachine.run suppressedRevealProgram x initial n).2) := by
  exact ⟨suppressed_reveal_simulates, suppressed_query_fresh⟩
