-- Prove2me | solution 1 for BianchiIX.hasDerivAt_projectiveField_boundary
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:48:02.697471+00:00
-- url     : https://prove2.me/submissions/1530e47c-358c-4a9c-8ac8-0a513117fd95

import Definitions.Def_BianchiIX_Dynamics_ProjectiveLinearization
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

noncomputable section
open BianchiIX


theorem solution {gamma : ℝ → ProjectiveState}
    {xi : ProjectiveState} {t m v : ℝ}
    (hg : HasDerivAt gamma xi t) (hb : gamma t = ![m, 0, v, 0]) :
    HasDerivAt (fun s => projectiveField (gamma s)) (projectiveBoundaryVariation m v xi) t := by
  have hm := hasDerivAt_pi.mp hg 0
  have hu := hasDerivAt_pi.mp hg 1
  have hv := hasDerivAt_pi.mp hg 2
  have hw := hasDerivAt_pi.mp hg 3
  have hc := hu.mul ((hv.add hw).sub hu)
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert! ((((hv.pow 2).neg.add (hw.pow 2)).add (hu.mul (hv.sub hw))).sub (hm.mul hc)) using 1
    dsimp [projectiveBoundaryVariation]
    simp only [hb]
    dsimp
    ring
  · convert! (((((hm.pow 2).const_sub 1).sub ((hv.sub hw).pow 2)).add (hu.pow 2)).mul hu).div_const 2 using 1
    dsimp [projectiveBoundaryVariation]
    simp only [hb]
    dsimp
    ring
  · convert! (((hm.sub_const 1).sub hc).mul hv) using 1
    dsimp [projectiveBoundaryVariation]
    simp only [hb]
    dsimp
    ring
  · convert! (((hm.neg.sub_const 1).sub hc).mul hw) using 1
    dsimp [projectiveBoundaryVariation]
    simp only [hb]
    dsimp
    ring
