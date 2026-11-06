-- Prove2me | solution 1 for BianchiIX.hasDerivAt_stateConstraint
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T13:58:51.497998+00:00
-- url     : https://prove2.me/submissions/8516608e-a0e4-4e33-b8fb-3093098a135e

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Theorems.Thm_BianchiIX_hasDerivAt_constraint
import Theorems.Thm_BianchiIX_hasDerivAt_normalized_components
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

noncomputable section
open BianchiIX
open Set


theorem solution {α : ℝ → NormalizedState} {t : ℝ}
    (hα : HasDerivAt α (normalizedField (α t)) t) :
    HasDerivAt (fun u => stateConstraint (α u)) 0 t := by
  obtain ⟨hp, hs, ha, hb, hc⟩ := hasDerivAt_normalized_components hα
  exact hasDerivAt_constraint hp hs ha hb hc
