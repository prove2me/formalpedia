-- Prove2me | solution 1 for BianchiIX.referenceForcedVariation_transverse
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:02:21.046098+00:00
-- url     : https://prove2.me/submissions/8e83e22a-c429-4dce-9ee7-23888fff9636

import Definitions.Def_BianchiIX_Dynamics_ProjectiveLinearization
import Definitions.Def_BianchiIX_Dynamics_ReferenceVariation
import Definitions.Def_BianchiIX_Dynamics_ReferenceScattering
import Theorems.Thm_BianchiIX_hasDerivAt_referenceStrongMode
import Theorems.Thm_BianchiIX_hasDerivAt_referenceWeakMode
import Theorems.Thm_BianchiIX_homogeneous_solution_eq_mode_ratio
import Theorems.Thm_BianchiIX_referenceTransverseMode_pos
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


theorem solution {I : Set ℝ} (hI : Convex ℝ I)
    {k : ℝ} {xi : ℝ → ProjectiveState} {a : ℝ → ℝ}
    (hxi : ∀ t ∈ I, HasDerivAt xi (referenceVariationVelocity k t (xi t) (a t)) t)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    xi t 1 = xi s 1 * (referenceTransverseMode k (k ^ 2 / 2) t /
      referenceTransverseMode k (k ^ 2 / 2) s) ∧
    xi t 3 = xi s 3 * (referenceTransverseMode k 2 t / referenceTransverseMode k 2 s) := by
  have hu (u : ℝ) (hu : u ∈ I) : HasDerivAt (fun v => xi v 1)
      (((1 - (referencePulse k u 0) ^ 2 - (referencePulse k u 2) ^ 2) / 2) * xi u 1) u := by
    have H := hasDerivAt_pi.mp (hxi u hu) 1
    rw [referenceVariationVelocity_eq] at H
    simpa [projectiveBoundaryVariation, projectiveField, strongVelocity, referencePulse] using H
  have hw (u : ℝ) (hu : u ∈ I) : HasDerivAt (fun v => xi v 3)
      ((-referencePulse k u 0 - 1) * xi u 3) u := by
    have H := hasDerivAt_pi.mp (hxi u hu) 3
    rw [referenceVariationVelocity_eq] at H
    simpa [projectiveBoundaryVariation, projectiveField, weakVelocity, referencePulse] using H
  exact ⟨homogeneous_solution_eq_mode_ratio hI hu (fun u _ => hasDerivAt_referenceStrongMode k u)
      (fun u _ => ne_of_gt (referenceTransverseMode_pos k (k ^ 2 / 2) u)) hs ht,
    homogeneous_solution_eq_mode_ratio hI hw (fun u _ => hasDerivAt_referenceWeakMode k u)
      (fun u _ => ne_of_gt (referenceTransverseMode_pos k 2 u)) hs ht⟩
