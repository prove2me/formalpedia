-- Prove2me | solution 1 for ConicQuadIPM.NewtonStep.p14_first_eq
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T03:52:39.990111+00:00
-- url     : https://prove2.me/submissions/791856f1-b877-49eb-904a-12bb6e64cc3b

import Mathlib
import Definitions.Def_ConicQuadIPM_NewtonStep_Setting
import Theorems.Thm_ConicQuadIPM_NewtonStep_eq_61

open Matrix ConicQuadIPM.Complementarity

private lemma first_dot {d : ℕ} (v : Fin (d + 1) → ℝ) : e1 ⬝ᵥ v = v 0 := by
  simp [e1, dotProduct, Fin.sum_univ_succ]

private lemma arrow_first {d : ℕ} (v w : Fin d → ℝ) :
    e1 ⬝ᵥ (arrow v *ᵥ w) = v ⬝ᵥ w := by
  cases d with
  | zero => simp [dotProduct]
  | succ d =>
      rw [first_dot]
      simp [mulVec, dotProduct, arrow]

theorem solution
    {k : ℕ} (kind : Fin k → ConicQuadIPM.Complementarity.ConeKind) (n : Fin k → ℕ) (hwf : ConicQuadIPM.Complementarity.WellFormed kind n)
    (x0 s0 dx ds : (i : Fin k) → Fin (n i) → ℝ) (τ0 κ0 dτ dκ : ℝ) :
    (∑ i, x0 i ⬝ᵥ ds i) + (∑ i, s0 i ⬝ᵥ dx i) + τ0 * dκ + κ0 * dτ
      = (∑ i, ConicQuadIPM.Complementarity.e1 ⬝ᵥ (ConicQuadIPM.Complementarity.arrow (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ x0 i) *ᵥ (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ ds i)
            + ConicQuadIPM.Complementarity.arrow (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ s0 i) *ᵥ (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ dx i)))
        + τ0 * dκ + κ0 * dτ := by
  simp_rw [dotProduct_add, arrow_first]
  rw [Finset.sum_add_distrib,
    (ConicQuadIPM.NewtonStep.eq_61 kind n hwf x0 ds).2,
    (ConicQuadIPM.NewtonStep.eq_61 kind n hwf s0 dx).2]

#print axioms solution
