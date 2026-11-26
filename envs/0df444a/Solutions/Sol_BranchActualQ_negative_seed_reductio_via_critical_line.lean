-- Prove2me | solution 1 for BranchActualQ.negative_seed_reductio_via_critical_line
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T10:58:09.409262+00:00
-- url     : https://prove2.me/submissions/05aa1077-b23e-4592-adda-4df8dc255f15

import Theorems.Thm_BranchActualQ_negative_seed_excluded_in_both_branches
import Theorems.Thm_BranchActualQ_nonnegative_from_verified_height

theorem solution :
    let f : ℂ → ℂ := fun s => (1+s*(s-1)*completedRiemannZeta₀ s)/2
    let G : ℝ → ℝ := fun x => (f (1/2+(Real.sqrt x : ℂ))).re
    let Q : ℕ → ℝ → ℝ := fun n u =>
      (2 : ℝ)^n*u^(2*n-1)*(-1 : ℝ)^(n-1)*
        iteratedDeriv n (fun x => Real.log (G x)-Real.log (G 0)) (u^2)
    let S : Prop := ∃ (n : ℕ), 1 ≤ n ∧ ∃ u > 0, Q n u < 0
    let R : Prop := ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1/2
    let P : Prop := ∀ (n : ℕ), 1 ≤ n → ∀ u > 0, 0 ≤ Q n u
    (S → R) ∧ (R → P) ∧ (¬ S) ∧ P := by
  dsimp only
  let O : Set ℂ := {s | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ s.re ≠ 1/2}
  have seedToLine := fun hs (s : ℂ) (hz : riemannZeta s = 0) (h0 : 0 < s.re) (h1 : s.re < 1) => by
    show s.re = 1/2
    by_contra hOff
    have memO : s ∈ O := ⟨hz, h0, h1, hOff⟩
    by_cases hfin : O.Finite
    · exact BranchActualQ.negative_seed_excluded_in_both_branches.1 hs hfin ⟨s, memO⟩
    · exact BranchActualQ.negative_seed_excluded_in_both_branches.2 hs hfin
  have lineToTower := fun (hr : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1/2) =>
    BranchActualQ.nonnegative_from_verified_height (fun s hz h0 h1 _ => hr s hz h0 h1)
  have noSeed := fun hs => by
    show False
    have p := lineToTower (seedToLine hs)
    obtain ⟨n, hn, u, hu, hneg⟩ := hs
    exact (not_lt_of_ge (p n hn u hu)) hneg
  refine ⟨seedToLine, lineToTower, noSeed, ?_⟩
  intro n hn u hu
  exact le_of_not_gt (fun hneg => noSeed ⟨n, hn, u, hu, hneg⟩)
#print axioms solution
