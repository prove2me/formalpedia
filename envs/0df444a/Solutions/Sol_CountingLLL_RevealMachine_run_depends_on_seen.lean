-- Prove2me | solution 1 for CountingLLL.RevealMachine.run_depends_on_seen
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:48:45.275183+00:00
-- url     : https://prove2.me/submissions/a80854c5-a22b-4932-a09c-55a534f0b469

import Definitions.Def_CountingLLL_RevealMachine
set_option autoImplicit false
open CountingLLL.RevealMachine

private theorem seen_mono {σ ι α : Type*} [DecidableEq ι] (P : Program σ ι α)
    (ω : ι → α) (c : σ × Finset ι) : c.2 ⊆ (step P ω c).2 := by
  unfold step
  split <;> simp

theorem solution {σ ι α : Type*} [DecidableEq ι] (P : Program σ ι α)
    (ω ω' : ι → α) (initial : σ) (n : ℕ)
    (h : ∀ i ∈ (run P ω initial n).2, ω i = ω' i) :
    run P ω initial n = run P ω' initial n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hrs (x : ι → α) : run P x initial (n+1) = step P x (run P x initial n) := by
      simp [run, Function.iterate_succ_apply']
    have hsub : (run P ω initial n).2 ⊆ (run P ω initial (n+1)).2 := by
      rw [hrs]
      exact seen_mono P ω _
    have hprev : ∀ i ∈ (run P ω initial n).2, ω i = ω' i := by
      intro i hi; exact h i (hsub hi)
    have heq := ih hprev
    rw [hrs, hrs, ← heq]
    let c := run P ω initial n
    change step P ω c = step P ω' c
    by_cases hq : P.query c.1 = none
    · simp [step, hq]
    · obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hq
      have ha_seen : a ∈ (run P ω initial (n+1)).2 := by
        rw [hrs]
        change a ∈ (step P ω c).2
        simp [step, ha]
      have hv := h a ha_seen
      simp [step, ha, hv]

