-- Prove2me | solution 1 for BianchiIX.referenceVariation_scattering
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:05:18.170183+00:00
-- url     : https://prove2.me/submissions/95b9abd8-7f8b-4fd3-bec6-ff754a9fe228

import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
import Definitions.Def_BianchiIX_Dynamics_ReferenceVariation
import Definitions.Def_BianchiIX_Dynamics_ReferenceScattering
import Theorems.Thm_BianchiIX_referenceCoreGap_pos
import Theorems.Thm_BianchiIX_referenceForcedVariation_transverse
import Theorems.Thm_BianchiIX_referencePulse_entry
import Theorems.Thm_BianchiIX_referencePulse_exit
import Theorems.Thm_BianchiIX_referenceStrongMode_ratio
import Theorems.Thm_BianchiIX_referenceVariationInvariant_constant
import Theorems.Thm_BianchiIX_referenceWeakMode_ratio
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


/-- The first integral eliminates both the phase quadrature and tangent time corrections. -/
theorem solution {I : Set ℝ} (hI : Convex ℝ I)
    {k : ℝ} (hk : 1 < k) {xi : ℝ → ProjectiveState} {a : ℝ → ℝ}
    (hxi : ∀ t ∈ I, HasDerivAt xi (referenceVariationVelocity k t (xi t) (a t)) t)
    (hin : -referenceHalfTime k ∈ I) (hout : referenceHalfTime k ∈ I)
    (hsection : xi (-referenceHalfTime k) 2 = 0) :
    referenceExitProjection k (xi (referenceHalfTime k)) =
      ![-xi (-referenceHalfTime k) 0 +
          (2 / Real.sqrt (k ^ 2 - 1)) * (1 - Real.exp (-k * Real.arcosh k)) *
            xi (-referenceHalfTime k) 1,
        Real.exp (-k * Real.arcosh k) * xi (-referenceHalfTime k) 1,
        0, Real.exp (-4 * Real.arcosh k / k) * xi (-referenceHalfTime k) 3] := by
  have he := referenceVariationInvariant_constant hI hxi hin hout
  have htw := referenceForcedVariation_transverse hI hxi hin hout
  rw [referenceStrongMode_ratio hk, referenceWeakMode_ratio] at htw
  dsimp [referenceVariationInvariant] at he
  rw [referencePulse_entry hk, referencePulse_exit hk] at he
  dsimp at he
  rw [hsection, htw.1] at he
  have hd := ne_of_gt (referenceCoreGap_pos hk)
  ext i
  fin_cases i
  · dsimp [referenceExitProjection]
    field_simp
    simp only [neg_mul] at he ⊢
    linear_combination -(1 / 2) * he
  · exact htw.1.trans (mul_comm _ _)
  · rfl
  · exact htw.2.trans (mul_comm _ _)
