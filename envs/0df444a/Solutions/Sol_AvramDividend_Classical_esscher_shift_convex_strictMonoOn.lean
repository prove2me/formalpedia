-- Prove2me | solution 1 for AvramDividend.Classical.esscher_shift_convex_strictMonoOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T14:42:14.369324+00:00
-- url     : https://prove2.me/submissions/57821072-cd40-45b7-8307-15da65d59497

import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- Convexity and a positive Esscher root force strict monotonicity after the root. -/
theorem solution
    (psi : ℝ → ℝ) (phi q : ℝ)
    (hconv : ConvexOn ℝ (Ici (0 : ℝ)) psi)
    (hpsi0 : psi 0 = 0) (hphi : 0 < phi)
    (hq : 0 < q) (hpsiphi : psi phi = q) :
    StrictMonoOn (fun beta : ℝ => psi (phi + beta) - q) (Ici 0) := by
  have hroot : psi 0 < psi phi := by
    rw [hpsi0, hpsiphi]
    exact hq
  have hpsi : StrictMonoOn psi (Ici (0 : ℝ) ∩ Ici phi) :=
    hconv.strictMonoOn (by simp) hphi hroot
  intro a ha b hb hab
  have ha0 : 0 ≤ a := ha
  have hb0 : 0 ≤ b := hb
  have hxa : phi + a ∈ Ici (0 : ℝ) ∩ Ici phi := by
    change 0 ≤ phi + a ∧ phi ≤ phi + a
    constructor <;> linarith
  have hxb : phi + b ∈ Ici (0 : ℝ) ∩ Ici phi := by
    change 0 ≤ phi + b ∧ phi ≤ phi + b
    constructor <;> linarith
  have hmono := hpsi hxa hxb (by linarith : phi + a < phi + b)
  exact sub_lt_sub_right hmono q
