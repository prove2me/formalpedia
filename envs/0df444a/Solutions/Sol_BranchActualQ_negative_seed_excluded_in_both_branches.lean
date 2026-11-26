-- Prove2me | solution 1 for BranchActualQ.negative_seed_excluded_in_both_branches
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T10:55:09.603074+00:00
-- url     : https://prove2.me/submissions/da3c1b35-bdf1-4cab-80ba-4d9a54e3c220

import Theorems.Thm_BranchActualQ_nonnegative_unconditional

theorem solution :
    let f : ℂ → ℂ := fun s => (1+s*(s-1)*completedRiemannZeta₀ s)/2
    let G : ℝ → ℝ := fun x => (f (1/2+(Real.sqrt x : ℂ))).re
    let Q : ℕ → ℝ → ℝ := fun n u =>
      (2 : ℝ)^n*u^(2*n-1)*(-1 : ℝ)^(n-1)*
        iteratedDeriv n (fun x => Real.log (G x)-Real.log (G 0)) (u^2)
    let S : Prop := ∃ (n : ℕ), 1 ≤ n ∧ ∃ u > 0, Q n u < 0
    let O : Set ℂ := {s | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ s.re ≠ 1/2}
    (S → O.Finite → O.Nonempty → False) ∧ (S → O.Infinite → False) := by
  dsimp only
  constructor
  · rintro ⟨n, hn, u, hu, hneg⟩ _ _
    exact (not_lt_of_ge (BranchActualQ.nonnegative_unconditional n hn u hu)) hneg
  · rintro ⟨n, hn, u, hu, hneg⟩ _
    exact (not_lt_of_ge (BranchActualQ.nonnegative_unconditional n hn u hu)) hneg
#print axioms solution
