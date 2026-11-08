-- Prove2me | solution 1 for FuchsVdGraaf.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:27:44.343199+00:00
-- url     : https://prove2.me/submissions/7eb1bf96-ba9e-4be3-a89f-caf06f9d2f0e

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsProbDist
import Definitions.Def_FuchsVdGraaf_errorProb
import Definitions.Def_FuchsVdGraaf_kolmogorov

open FuchsVdGraaf in
theorem solution {X : Type} [Fintype X] (p0 p1 : X → ℝ)
    (hp0 : IsProbDist p0) (hp1 : IsProbDist p1) :
    errorProb p0 p1 = 1 / 2 - 1 / 2 * kolmogorov p0 p1 := by
  unfold errorProb kolmogorov
  have hterm : ∀ x, min (p0 x) (p1 x) = (p0 x + p1 x - |p0 x - p1 x|) / 2 := by
    intro x
    rcases le_total (p0 x) (p1 x) with h | h
    · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
    · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
  simp only [hterm]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib, hp0.2, hp1.2]
  ring
