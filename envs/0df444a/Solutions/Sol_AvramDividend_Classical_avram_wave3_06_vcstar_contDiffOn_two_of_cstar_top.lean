-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_06_vcstar_contDiffOn_two_of_cstar_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:49:44.829421+00:00
-- url     : https://prove2.me/submissions/c823b16b-1a2a-4a23-afe2-9b49cb142360

import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- An infinite candidate barrier selects the zero real barrier,
whose value is affine on strictly positive reserves. -/
theorem solution
    (W : ℝ → ℝ) (htop : cstar W = ⊤) :
    ContDiffOn ℝ 2 (vcstar W) (Ioi 0) := by
  have hAff : ContDiffOn ℝ 2
      (fun x : ℝ => x + divE (W 0) (scaleDeriv W 0)) (Ioi (0 : ℝ)) := by
    fun_prop
  have hEq : EqOn (vcstar W)
      (fun x : ℝ => x + divE (W 0) (scaleDeriv W 0)) (Ioi (0 : ℝ)) := by
    intro x hx
    have hx0 : 0 < x := hx
    simp [vcstar, barrierValue, htop, not_lt_of_ge (le_of_lt hx0),
      not_le_of_gt hx0]
  exact hAff.congr hEq
