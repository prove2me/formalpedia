-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.reciprocal_query_fresh
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:52:57.597429+00:00
-- url     : https://prove2.me/submissions/2b93a6d7-9c89-48ca-a478-df9a313fa93d

import Definitions.Def_CountingLLL_ReciprocalReveal
set_option autoImplicit false
open CountingLLL.ReciprocalTest CountingLLL.RevealMachine

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
    (h : FreshInv (s,S)) : FreshInv (CountingLLL.RevealMachine.step revealProgram x (s,S)) := by
  cases hp : s.phase with
  | start =>
    have hc := counts_step (uniformEntropy (x (.inr (.inl s.fairUsed)))) s
    simp only [oracleInc, fairInc, uniformInc, hp, Nat.add_zero] at hc
    simpa [CountingLLL.RevealMachine.step, revealProgram, readIndex, hp] using inv_fair s _ S h hc.1 hc.2.1 hc.2.2
  | initialCheck =>
    have hc := counts_step (uniformEntropy (x (.inr (.inl s.fairUsed)))) s
    simp only [oracleInc, fairInc, uniformInc, hp, Nat.add_zero] at hc
    simpa [CountingLLL.RevealMachine.step, revealProgram, readIndex, hp] using inv_fair s _ S h hc.1 hc.2.1 hc.2.2
  | loop =>
    have hc := counts_step (uniformEntropy 0) s
    simp only [oracleInc, fairInc, uniformInc, hp, Nat.add_zero] at hc
    simpa [CountingLLL.RevealMachine.step, revealProgram, readIndex, hp] using inv_silent s _ S h hc.1 hc.2.1 hc.2.2
  | coinOracle k =>
    have hc := counts_step (uniformEntropy (x (.inl s.oracleUsed))) s
    simp only [oracleInc, fairInc, uniformInc, hp, Nat.add_zero] at hc
    simpa [CountingLLL.RevealMachine.step, revealProgram, readIndex, hp] using inv_oracle s _ S h hc.1 hc.2.1 hc.2.2
  | coinFair k =>
    have hc := counts_step (uniformEntropy (x (.inr (.inl s.fairUsed)))) s
    simp only [oracleInc, fairInc, uniformInc, hp, Nat.add_zero] at hc
    simpa [CountingLLL.RevealMachine.step, revealProgram, readIndex, hp] using inv_fair s _ S h hc.1 hc.2.1 hc.2.2
  | uniformCheck =>
    have hc := counts_step (uniformEntropy (x (.inr (.inr (s.j-1,s.uniformUsed))))) s
    simp only [oracleInc, fairInc, uniformInc, hp, Nat.add_zero] at hc
    simpa [CountingLLL.RevealMachine.step, revealProgram, readIndex, hp] using inv_uniform s _ S h hc.1 hc.2.1 hc.2.2
  | done b =>
    have hc := counts_step (uniformEntropy 0) s
    simp only [oracleInc, fairInc, uniformInc, hp, Nat.add_zero] at hc
    simpa [CountingLLL.RevealMachine.step, revealProgram, readIndex, hp] using inv_silent s _ S h hc.1 hc.2.1 hc.2.2

private theorem invariant_run (x : ReadIndex → ℕ) (n : ℕ) :
    FreshInv (CountingLLL.RevealMachine.run revealProgram x initial n) := by
  induction n with
  | zero => simp [CountingLLL.RevealMachine.run, FreshInv]
  | succ n ih =>
    have hr : CountingLLL.RevealMachine.run revealProgram x initial (n+1) =
        CountingLLL.RevealMachine.step revealProgram x (CountingLLL.RevealMachine.run revealProgram x initial n) := by
      simp [CountingLLL.RevealMachine.run, Function.iterate_succ_apply']
    rw [hr]
    generalize hc : CountingLLL.RevealMachine.run revealProgram x initial n = c at *
    obtain ⟨s,S⟩ := c
    exact invariant_step x s S ih

/-- Every query of the encoded ReciprocalTest uses an unseen coordinate. -/
theorem solution (x : ReadIndex → ℕ) (n : ℕ) (a : ReadIndex)
    (h : readIndex (CountingLLL.RevealMachine.run revealProgram x initial n).1 = some a) :
    a ∉ (CountingLLL.RevealMachine.run revealProgram x initial n).2 := by
  have hinv := invariant_run x n
  let c := CountingLLL.RevealMachine.run revealProgram x initial n
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
