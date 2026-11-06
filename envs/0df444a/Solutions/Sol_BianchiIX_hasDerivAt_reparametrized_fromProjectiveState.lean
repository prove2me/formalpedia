-- Prove2me | solution 1 for BianchiIX.hasDerivAt_reparametrized_fromProjectiveState
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:33:57.501913+00:00
-- url     : https://prove2.me/submissions/8630b776-6585-4204-bcbd-2cc386430d43

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Theorems.Thm_BianchiIX_hasDerivAt_fromProjectiveState
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


theorem solution {β : ℝ → ProjectiveState}
    {clock : ℝ → ℝ} {t : ℝ}
    (hβ : HasDerivAt β (projectiveField (β (clock t))) (clock t))
    (hD : projectiveStateDenom (β (clock t)) ≠ 0)
    (hclock : HasDerivAt clock (6 / projectiveStateDenom (β (clock t))) t) :
    HasDerivAt (fun u => fromProjectiveState (β (clock u)))
      (normalizedField (fromProjectiveState (β (clock t)))) t := by
  have h := (hasDerivAt_fromProjectiveState hβ hD).scomp t hclock
  have hscale : (6 / projectiveStateDenom (β (clock t))) *
      (projectiveStateDenom (β (clock t)) / 6) = 1 := by field_simp
  simp only [smul_smul, hscale, one_smul] at h
  convert! h using 1
