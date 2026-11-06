-- Prove2me | solution 1 for BianchiIX.hasDerivAt_referenceVariationInvariant
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:01:55.487197+00:00
-- url     : https://prove2.me/submissions/ffb14b09-feef-4993-80bf-9ffbadabcb97

import Definitions.Def_BianchiIX_Dynamics_ProjectiveLinearization
import Definitions.Def_BianchiIX_Dynamics_ReferenceScattering
import Theorems.Thm_BianchiIX_hasDerivAt_referencePulse
import Theorems.Thm_BianchiIX_referenceVariationVelocity_eq
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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique

noncomputable section
open BianchiIX
open Set


theorem solution {k t a : ℝ} {xi : ℝ → ProjectiveState}
    (hxi : HasDerivAt xi (referenceVariationVelocity k t (xi t) a) t) :
    HasDerivAt (fun s => referenceVariationInvariant k s (xi s)) 0 t := by
  have hm := hasDerivAt_pi.mp (hasDerivAt_referencePulse k t) 0
  have hv := hasDerivAt_pi.mp (hasDerivAt_referencePulse k t) 2
  have hx := hasDerivAt_pi.mp hxi
  have H := ((((hm.sub_const 1).const_mul 2).mul (hx 0)).add
    ((hv.const_mul 2).mul (hx 2))).sub ((hv.const_mul 4).mul (hx 1))
  convert! H using 1
  rw [referenceVariationVelocity_eq]
  dsimp [projectiveBoundaryVariation, referencePulse, projectiveField,
    phaseVelocity, strongVelocity, activeVelocity, weakVelocity, coupling]
  ring
