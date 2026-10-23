-- Prove2me | solution 1 for AvramDividend.Classical.barrierValue_deriv_one_of_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:16:20.983753+00:00
-- url     : https://prove2.me/submissions/0a06a06e-016e-4e0f-b315-1ed530cbb66a

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_barrierValue_above_affine

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set

theorem solution
    (W : ℝ → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hdiff : DifferentiableAt ℝ (barrierValue W a) a) :
    deriv (barrierValue W a) a = 1 := by
  let g : ℝ → ℝ := fun x => (x - a) + barrierValue W a a
  have hg : HasDerivWithinAt g 1 (Ici a) a := by
    have hga : HasDerivAt g 1 a := by
      simpa [g] using
        ((hasDerivAt_id a).sub_const a).add_const (barrierValue W a a)
    exact hga.hasDerivWithinAt
  have hEq : ∀ x ∈ Ici a, barrierValue W a x = g x := by
    intro x hx
    have hax : a ≤ x := Set.mem_Ici.mp hx
    rcases eq_or_lt_of_le hax with hxa | hxa
    · subst x
      simp [g]
    · simpa [g] using barrierValue_above_affine W a x ha hxa
  have hbarrier : HasDerivWithinAt (barrierValue W a) 1 (Ici a) a :=
    hg.congr hEq (by simp [g])
  have hfromDiff : HasDerivWithinAt (barrierValue W a)
      (deriv (barrierValue W a) a) (Ici a) a :=
    hdiff.hasDerivAt.hasDerivWithinAt
  have hone := hbarrier.derivWithin (uniqueDiffWithinAt_Ici a)
  have hactual := hfromDiff.derivWithin (uniqueDiffWithinAt_Ici a)
  exact hactual.symm.trans hone
