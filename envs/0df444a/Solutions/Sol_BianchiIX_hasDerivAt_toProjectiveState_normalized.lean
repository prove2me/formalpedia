-- Prove2me | solution 1 for BianchiIX.hasDerivAt_toProjectiveState_normalized
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:32:01.261366+00:00
-- url     : https://prove2.me/submissions/59bed808-0de4-4876-9ecd-7315394c49ee

import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Theorems.Thm_BianchiIX_hasDerivAt_normalized_components
import Theorems.Thm_BianchiIX_hasDerivAt_projective_flow
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


theorem solution {alpha : ℝ → NormalizedState} {t : ℝ}
    (hα : HasDerivAt alpha (normalizedField (alpha t)) t)
    (hA : 1 + alpha t 0 ≠ 0) (hc : stateConstraint (alpha t) = 1) :
    HasDerivAt (fun s => toProjectiveState (alpha s))
      ((1 + alpha t 0) • projectiveField (toProjectiveState (alpha t))) t := by
  obtain ⟨hp, hs, ha, hb, hw⟩ := hasDerivAt_normalized_components hα
  obtain ⟨hm, hu, hv, hw⟩ := hasDerivAt_projective_flow
    (p := fun s => alpha s 0) (s := fun s => alpha s 1)
    (a := fun s => alpha s 2) (b := fun s => alpha s 3) (c := fun s => alpha s 4)
    hp hs ha hb hw hA hc
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hm
  · exact hu
  · exact hv
  · exact hw
