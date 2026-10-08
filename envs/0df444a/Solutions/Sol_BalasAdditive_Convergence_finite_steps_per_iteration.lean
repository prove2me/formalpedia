-- Prove2me | solution 1 for BalasAdditive.Convergence.finite_steps_per_iteration
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T13:52:53.356079+00:00
-- url     : https://prove2.me/submissions/1799ca5f-8fc9-4903-bc29-6dbdf792c0e0

import Mathlib
import Definitions.Def_BalasAdditive_Convergence_Algorithm

set_option autoImplicit false


namespace BalasAdditive.Convergence

theorem step_cases {n m : ℕ} (P : Problem n m) (σ τ : State n) (h : Step P σ τ) :
    τ.history = σ.history ∨ ∃ p X Y, τ = appendSolution P σ p X Y := by
  cases h <;> first
    | (left; rfl)
    | (right; exact ⟨_, _, _, rfl⟩)

theorem newN_feasible {n m : ℕ} (P : Problem n m) (h : List (Record n))
    (cs : List (Finset (Fin n))) (J : Finset (Fin n)) (hf : P.lp.Feasible J) :
    newN P h cs J = ∅ := by
  unfold newN
  apply Finset.filter_false_of_mem
  intro j _ hj
  apply hj.2.2
  intro i hi
  exact absurd (hf i) (not_le.mpr hi)

theorem noimp_core {n m : ℕ} (P : Problem n m) (σ : State n) (hr : Reachable P σ) :
    ∀ p, p < σ.history.length → P.lp.Feasible (σ.J p) → σ.N p = ∅ := by
  induction hr with
  | refl =>
    intro p hp hf
    simp [init] at hp
    subst hp
    simp [init, State.J, State.N] at hf ⊢
    exact newN_feasible P [] [] ∅ hf
  | @tail σ0 τ _ hstep ih =>
    rcases step_cases P σ0 τ hstep with h | ⟨p0, X, Y, rfl⟩
    · intro p hp hf
      have e1 : τ.J p = σ0.J p := by simp [State.J, h]
      have e2 : τ.N p = σ0.N p := by simp [State.N, h]
      rw [e2]; rw [h] at hp; rw [e1] at hf
      exact ih p hp hf
    · intro p hp hf
      simp only [appendSolution, List.length_append, List.length_singleton] at hp
      by_cases hlt : p < σ0.history.length
      · have e1 : (appendSolution P σ0 p0 X Y).J p = σ0.J p := by
          simp [appendSolution, State.J, List.getElem?_append_left hlt]
        have e2 : (appendSolution P σ0 p0 X Y).N p = σ0.N p := by
          simp [appendSolution, State.N, List.getElem?_append_left hlt]
        rw [e2]; rw [e1] at hf
        exact ih p hlt hf
      · have hp' : p = σ0.history.length := by omega
        subst hp'
        simp [appendSolution, State.J, State.N] at hf ⊢
        exact newN_feasible P _ _ _ hf

theorem feasible_solution_no_improving_core {n m : ℕ} (P : Problem n m) (σ : State n)
    (hr : Reachable P σ) (p : ℕ) (hp : p < σ.history.length)
    (hfeas : P.lp.Feasible (σ.J p)) :
    σ.N p = ∅ := noimp_core P σ hr p hp hfeas

def mu {n : ℕ} (L : ℕ) (s : State n) : ℕ := match s.phase with
    | .start => L + 2
    | .scan b => b + 1
    | .stopped => 0

theorem mu_dec {n m : ℕ} (P : Problem n m) (σ τ : State n) (h : Step P σ τ)
    (hlen : τ.history.length = σ.history.length) :
    mu σ.history.length τ < mu σ.history.length σ := by
  cases h with
  | one_a hph hf => simp [mu, hph, beginScan]
  | two_a hph hb he => simp [mu, hph, beginScan]
  | three_a hph hb hn hf => simp [mu, hph, beginScan]
  | three_b j hph hb hn hs' hc => simp [appendSolution] at hlen
  | four_a hph hb hn hh hn' hc => simp [appendSolution] at hlen
  | four_b hph hb hn hh hn' hc => simp [mu, hph, beginScan]
  | five_a b hph hn => simp [mu, hph, stop]
  | six_a b k hph hsel hf =>
    have := hsel.1.1
    simp [mu, hph, beginScan]; omega
  | six_b b k j hph hsel hs' hc => simp [appendSolution] at hlen
  | seven_a b k hph hsel hh hn hc => simp [appendSolution] at hlen
  | seven_b b k hph hsel hh hn hc =>
    have := hsel.1.1
    simp [mu, hph, beginScan]; omega

theorem finite_steps_core {n m : ℕ} (P : Problem n m) (σ : State n) :
    ¬ ∃ run : ℕ → State n,
      run 0 = σ ∧
      (∀ t, Step P (run t) (run (t + 1))) ∧
      (∀ t, (run t).history.length = σ.history.length) := by
  rintro ⟨run, h0, hs, hl⟩
  have key : ∀ t, mu σ.history.length (run (t+1)) < mu σ.history.length (run t) := by
    intro t
    have := mu_dec P (run t) (run (t+1)) (hs t) (by rw [hl, hl])
    rwa [hl t] at this
  have : ∀ t, mu σ.history.length (run t) + t ≤ mu σ.history.length (run 0) := by
    intro t; induction t with
    | zero => simp
    | succ t ih => have := key t; omega
  have := this (mu σ.history.length (run 0) + 1)
  omega

end BalasAdditive.Convergence

open BalasAdditive.Convergence


theorem solution {n m : ℕ} (P : Problem n m) (σ : State n)
    (hr : Reachable P σ) :
    ¬ ∃ run : ℕ → State n,
      run 0 = σ ∧
      (∀ t, Step P (run t) (run (t + 1))) ∧
      (∀ t, (run t).history.length = σ.history.length) := by
  exact finite_steps_core P σ
