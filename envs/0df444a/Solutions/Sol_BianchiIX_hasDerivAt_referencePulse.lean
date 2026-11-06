-- Prove2me | solution 1 for BianchiIX.hasDerivAt_referencePulse
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:53:17.509391+00:00
-- url     : https://prove2.me/submissions/1fbe0e44-da04-43bc-864c-b8dd246ed014

import Definitions.Def_BianchiIX_Dynamics_ReferencePulse
import Theorems.Thm_BianchiIX_hasDerivAt_real_tanh
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
import Mathlib.Analysis.SpecialFunctions.Arcosh

noncomputable section
open BianchiIX


theorem solution (k t : ℝ) :
    HasDerivAt (referencePulse k) (projectiveField (referencePulse k t)) t := by
  have hz : HasDerivAt (fun s : ℝ => k * s) k t := by
    simpa using (hasDerivAt_id t).const_mul k
  have hm := (((hasDerivAt_real_tanh (k * t)).comp t hz).const_mul k).const_sub 1
  have hv := (hasDerivAt_const t k).div hz.cosh (ne_of_gt (Real.cosh_pos (k * t)))
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert! hm using 1
    dsimp [projectiveField, referencePulse, phaseVelocity, coupling]
    ring
  · convert! hasDerivAt_const t (0 : ℝ) using 1
    simp [projectiveField, referencePulse, strongVelocity]
  · convert! hv using 1
    dsimp [projectiveField, referencePulse, activeVelocity, coupling]
    rw [Real.tanh_eq_sinh_div_cosh]
    ring
  · convert! hasDerivAt_const t (0 : ℝ) using 1
    simp [projectiveField, referencePulse, weakVelocity]
