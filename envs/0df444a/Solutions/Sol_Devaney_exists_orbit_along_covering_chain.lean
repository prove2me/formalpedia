-- Prove2me | solution 1 for Devaney.exists_orbit_along_covering_chain
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T21:08:10.633905+00:00
-- url     : https://prove2.me/submissions/68a1eaa4-9dc5-4585-bd13-2f3760d90ee3

import Mathlib
import Definitions.Def_Devaney_sarkovskii

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace DevFix

open Devaney

/-- §1.10, second observation: a chain of covering intervals carries an orbit. -/
theorem exists_orbit_along_covering_chain (f : ℝ → ℝ) (hf : Continuous f) (n : ℕ)
    (a b : ℕ → ℝ) (hab : ∀ i ≤ n, a i ≤ b i)
    (hcov : ∀ i < n, Covers f (Set.Icc (a i) (b i)) (Set.Icc (a (i + 1)) (b (i + 1)))) :
    ∃ x ∈ Set.Icc (a 0) (b 0), ∀ i ≤ n, f^[i] x ∈ Set.Icc (a i) (b i) := by
  induction n generalizing a b with
  | zero =>
    refine ⟨a 0, Set.left_mem_Icc.2 (hab 0 le_rfl), ?_⟩
    intro i hi
    interval_cases i
    simpa using Set.left_mem_Icc.2 (hab 0 le_rfl)
  | succ n ih =>
    obtain ⟨y, hy0, hy⟩ :=
      ih (fun i => a (i + 1)) (fun i => b (i + 1))
        (fun i hi => hab (i + 1) (by omega)) (fun i hi => hcov (i + 1) (by omega))
    obtain ⟨x, hx0, hxy⟩ := hcov 0 (by omega) hy0
    refine ⟨x, hx0, ?_⟩
    intro i hi
    match i with
    | 0 => simpa using hx0
    | (j + 1) =>
      have := hy j (by omega)
      rwa [Function.iterate_succ_apply, hxy]

end DevFix

open Devaney in
theorem solution (f : ℝ → ℝ) (hf : Continuous f) (n : ℕ)
    (a b : ℕ → ℝ) (hab : ∀ i ≤ n, a i ≤ b i)
    (hcov : ∀ i < n, Covers f (Set.Icc (a i) (b i)) (Set.Icc (a (i + 1)) (b (i + 1)))) :
    ∃ x ∈ Set.Icc (a 0) (b 0), ∀ i ≤ n, f^[i] x ∈ Set.Icc (a i) (b i) :=
  DevFix.exists_orbit_along_covering_chain f hf n a b hab hcov
