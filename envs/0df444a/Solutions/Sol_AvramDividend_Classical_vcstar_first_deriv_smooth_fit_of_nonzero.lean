-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_first_deriv_smooth_fit_of_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T17:10:06.967031+00:00
-- url     : https://prove2.me/submissions/7730c1eb-f6f9-4c43-af52-1eb4d6dbbda7

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (W : ℝ → ℝ)
    (hc : 0 < (cstar W).toReal)
    (hWdiff : DifferentiableAt ℝ W (cstar W).toReal)
    (hWderiv : deriv W (cstar W).toReal ≠ 0) :
    deriv (vcstar W) (cstar W).toReal =
      deriv (fun z : ℝ => divE (W z) (scaleDeriv W (cstar W).toReal))
        (cstar W).toReal := by
  let c := (cstar W).toReal
  have hc' : 0 < c := hc
  have hcne : c ≠ 0 := hc'.ne'
  have hWdiffC : DifferentiableAt ℝ W c := hWdiff
  have hdne : deriv W c ≠ 0 := hWderiv
  have hscale : scaleDeriv W c = ((deriv W c : ℝ) : EReal) := by
    simp [scaleDeriv, hcne]
  have hdiv (y : ℝ) :
      divE (W y) (scaleDeriv W c) = W y / deriv W c := by
    simp [hscale, divE]
  have hL0 : HasDerivWithinAt (fun y : ℝ => W y / deriv W c) 1
      (Icc 0 c) c := by
    simpa [hdne] using
      (hWdiffC.hasDerivAt.div_const (deriv W c)).hasDerivWithinAt
  have hL : HasDerivWithinAt (vcstar W) 1 (Icc 0 c) c :=
    hL0.congr_of_mem (fun y hy => by
      change 0 ≤ y ∧ y ≤ c at hy
      simp [vcstar, barrierValue, c, not_lt.mpr hy.1, hy.2, hdiv])
        ⟨hc'.le, le_rfl⟩
  have hR0 : HasDerivWithinAt
      (fun y : ℝ => y - c + W c / deriv W c) 1 (Ici c) c := by
    simpa using (((hasDerivAt_id c).sub_const c).add_const
      (W c / deriv W c)).hasDerivWithinAt
  have hR : HasDerivWithinAt (vcstar W) 1 (Ici c) c :=
    hR0.congr_of_mem (fun y hy => by
      change c ≤ y at hy
      rcases eq_or_lt_of_le hy with rfl | hy'
      · simp [vcstar, barrierValue, c, hc'.le, hdiv]
      · have hy0 : 0 < y := hc'.trans hy'
        simp [vcstar, barrierValue, c, not_lt.mpr hy0.le,
          not_le.mpr hy', hdiv]) (by simp)
  have hu := hL.union hR
  rw [Icc_union_Ici_eq_Ici hc'.le] at hu
  have hd : HasDerivAt (vcstar W) 1 c :=
    hu.hasDerivAt (Ici_mem_nhds hc')
  have hdScaled : HasDerivAt
      (fun z : ℝ => W z / deriv W c) 1 c := by
    simpa [hdne] using hWdiffC.hasDerivAt.div_const (deriv W c)
  have hFunEq :
      (fun z : ℝ => divE (W z) (scaleDeriv W c)) =
        (fun z : ℝ => W z / deriv W c) := funext hdiv
  calc
    deriv (vcstar W) c = 1 := hd.deriv
    _ = deriv (fun z : ℝ => divE (W z) (scaleDeriv W c)) c := by
      rw [hFunEq]
      exact hdScaled.deriv.symm
