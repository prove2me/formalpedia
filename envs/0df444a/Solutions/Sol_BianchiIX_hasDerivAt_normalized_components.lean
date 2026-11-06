-- Prove2me | solution 1 for BianchiIX.hasDerivAt_normalized_components
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T13:57:47.062708+00:00
-- url     : https://prove2.me/submissions/b3bd3893-8b5d-4097-8681-d7b1a81622d4

import Definitions.Def_BianchiIX_Dynamics_Normalized
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
    HasDerivAt (fun u => α u 0) (shearPlus (α t 0) (α t 2) (α t 3) (α t 4)) t ∧
    HasDerivAt (fun u => α u 1) (shearMinus (α t 1) (α t 2) (α t 3) (α t 4)) t ∧
    HasDerivAt (fun u => α u 2) (rateOne (α t 0) (α t 1) * α t 2) t ∧
    HasDerivAt (fun u => α u 3) (rateTwo (α t 0) (α t 1) * α t 3) t ∧
    HasDerivAt (fun u => α u 4) (rateThree (α t 0) (α t 1) * α t 4) t :=
  ⟨hasDerivAt_pi.mp hα 0, hasDerivAt_pi.mp hα 1, hasDerivAt_pi.mp hα 2,
    hasDerivAt_pi.mp hα 3, hasDerivAt_pi.mp hα 4⟩
